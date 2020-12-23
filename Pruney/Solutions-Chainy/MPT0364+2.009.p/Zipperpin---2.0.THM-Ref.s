%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mCWxJvpaUX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 134 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  432 (1422 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ X10 ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X15 @ ( k3_subset_1 @ X14 @ X13 ) )
      | ( r1_xboole_0 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_xboole_0 @ X15 @ X13 )
      | ( r1_tarski @ X15 @ ( k3_subset_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','22','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X11 @ X10 ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ( r1_tarski @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['24','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mCWxJvpaUX
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 74 iterations in 0.028s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
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
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t31_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49           ( ( r1_tarski @ B @ C ) <=>
% 0.22/0.49             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.22/0.49          | ~ (r1_tarski @ X12 @ X10)
% 0.22/0.49          | (r1_tarski @ (k3_subset_1 @ X11 @ X10) @ (k3_subset_1 @ X11 @ X12))
% 0.22/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49             (k3_subset_1 @ sk_A @ X0))
% 0.22/0.49          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49           (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '9'])).
% 0.22/0.49  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t43_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.22/0.49             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.49          | ~ (r1_tarski @ X15 @ (k3_subset_1 @ X14 @ X13))
% 0.22/0.49          | (r1_xboole_0 @ X15 @ X13)
% 0.22/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49          | (r1_xboole_0 @ X0 @ sk_B)
% 0.22/0.49          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.49         | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.49  thf('15', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '17'])).
% 0.22/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.22/0.49         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.22/0.49       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 0.22/0.49  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.49          | ~ (r1_xboole_0 @ X15 @ X13)
% 0.22/0.49          | (r1_tarski @ X15 @ (k3_subset_1 @ X14 @ X13))
% 0.22/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.49        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.22/0.49           (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.22/0.49         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))
% 0.22/0.49         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.22/0.49       ((r1_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('34', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '22', '33'])).
% 0.22/0.49  thf('35', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.22/0.49          | ~ (r1_tarski @ (k3_subset_1 @ X11 @ X10) @ 
% 0.22/0.49               (k3_subset_1 @ X11 @ X12))
% 0.22/0.49          | (r1_tarski @ X12 @ X10)
% 0.22/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49        | (r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('41', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.49  thf('42', plain, ($false), inference('demod', [status(thm)], ['24', '41'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
