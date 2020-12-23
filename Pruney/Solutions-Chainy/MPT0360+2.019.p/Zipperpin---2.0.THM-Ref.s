%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BojvP4ZrqQ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 356 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    = ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BojvP4ZrqQ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 78 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(t40_subset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.49         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49          ( ( ( r1_tarski @ B @ C ) & 
% 0.21/0.49              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.21/0.49            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.21/0.49  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d5_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.21/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t79_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.49           = (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.21/0.49         = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.21/0.49         = (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t85_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X12 @ X13)
% 0.21/0.49          | (r1_xboole_0 @ X12 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, (((k1_xboole_0) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '17'])).
% 0.21/0.49  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
