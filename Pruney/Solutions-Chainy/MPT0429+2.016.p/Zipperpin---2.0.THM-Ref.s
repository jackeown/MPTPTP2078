%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8silXsexZ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:32 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :  158 ( 185 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ o_0_0_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t55_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B
          = ( k1_tarski @ A ) )
       => ( ( k7_setfam_1 @ A @ B )
          = ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
       != ( k1_tarski @ X7 ) )
      | ( ( k7_setfam_1 @ X7 @ X8 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t55_setfam_1])).

thf('9',plain,(
    ! [X7: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ( ( k7_setfam_1 @ X7 @ ( k1_tarski @ X7 ) )
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k7_setfam_1 @ X7 @ ( k1_tarski @ X7 ) )
      = ( k1_tarski @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ o_0_0_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['2','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8silXsexZ
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:29:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 24 iterations in 0.013s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.24/0.50  thf(t61_setfam_1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( m1_subset_1 @
% 0.24/0.50       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( m1_subset_1 @
% 0.24/0.50          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.24/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.24/0.50  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (~ (m1_subset_1 @ (k1_tarski @ o_0_0_xboole_0) @ 
% 0.24/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(t80_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X1 : $i]: (r1_tarski @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.24/0.50  thf(t3_subset, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X4 : $i, X6 : $i]:
% 0.24/0.50         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.50  thf(dt_k7_setfam_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.50       ( m1_subset_1 @
% 0.24/0.50         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]:
% 0.24/0.50         ((m1_subset_1 @ (k7_setfam_1 @ X2 @ X3) @ 
% 0.24/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2)))
% 0.24/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2))))),
% 0.24/0.50      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ X0)) @ 
% 0.24/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf(t55_setfam_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.50       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 0.24/0.50         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X7 : $i, X8 : $i]:
% 0.24/0.51         (((X8) != (k1_tarski @ X7))
% 0.24/0.51          | ((k7_setfam_1 @ X7 @ X8) = (k1_tarski @ k1_xboole_0))
% 0.24/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.24/0.51      inference('cnf', [status(esa)], [t55_setfam_1])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X7 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ (k1_tarski @ X7) @ 
% 0.24/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7)))
% 0.24/0.51          | ((k7_setfam_1 @ X7 @ (k1_tarski @ X7)) = (k1_tarski @ k1_xboole_0)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (m1_subset_1 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.51  thf('11', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X7 : $i]:
% 0.24/0.51         ((k7_setfam_1 @ X7 @ (k1_tarski @ X7)) = (k1_tarski @ o_0_0_xboole_0))),
% 0.24/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (m1_subset_1 @ (k1_tarski @ o_0_0_xboole_0) @ 
% 0.24/0.51          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.51      inference('demod', [status(thm)], ['7', '12'])).
% 0.24/0.51  thf('14', plain, ($false), inference('demod', [status(thm)], ['2', '13'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
