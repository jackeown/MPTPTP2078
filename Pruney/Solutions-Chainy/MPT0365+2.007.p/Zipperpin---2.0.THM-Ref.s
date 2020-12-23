%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35Jp38maln

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  326 ( 694 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( r1_xboole_0 @ B @ C )
              & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( r1_xboole_0 @ B @ C )
                & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_xboole_0 @ X10 @ X8 )
      | ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
    | ( ( k3_subset_1 @ sk_A @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_xboole_0 @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ X5 ) @ X7 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X6 @ X7 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['10','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35Jp38maln
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 73 iterations in 0.040s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.49  thf(t46_subset_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49           ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.19/0.49               ( r1_xboole_0 @
% 0.19/0.49                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.19/0.49             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49          ( ![C:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49              ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.19/0.49                  ( r1_xboole_0 @
% 0.19/0.49                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.19/0.49                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 0.19/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t43_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.19/0.49             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.19/0.49          | ~ (r1_xboole_0 @ X10 @ X8)
% 0.19/0.49          | (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.19/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.49          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.19/0.49          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((~ (r1_xboole_0 @ sk_B @ sk_C)
% 0.19/0.49        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.49  thf('5', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i, X2 : $i]:
% 0.19/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 0.19/0.49        | ((k3_subset_1 @ sk_A @ sk_C) = (sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('10', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('12', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t44_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.19/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.19/0.49          | ~ (r1_xboole_0 @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.19/0.49          | (r1_tarski @ X13 @ X11)
% 0.19/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t44_subset_1])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.49          | (r1_tarski @ X0 @ sk_C)
% 0.19/0.49          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.49        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_k3_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.19/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.19/0.49  thf('20', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t36_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.19/0.49             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.49          | (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ X7)
% 0.19/0.49          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X7) @ X5)
% 0.19/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.49          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ sk_C)
% 0.19/0.49          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 0.19/0.49        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.19/0.49  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('25', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain, ($false), inference('demod', [status(thm)], ['10', '25'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
