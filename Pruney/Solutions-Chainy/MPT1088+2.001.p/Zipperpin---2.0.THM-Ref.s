%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szEkTY830Z

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   86 ( 105 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc2_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_finset_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_finset_1 @ X4 )
      | ~ ( v1_finset_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ X0 )
      | ( v1_finset_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t16_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k6_subset_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k6_subset_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_finset_1])).

thf('5',plain,(
    ~ ( v1_finset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ~ ( v1_finset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szEkTY830Z
% 0.14/0.36  % Computer   : n018.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:02:27 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 7 iterations in 0.009s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.22/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.45  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.22/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(dt_k6_subset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (m1_subset_1 @ (k6_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.22/0.45  thf(redefinition_k6_subset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.45  thf(cc2_finset_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_finset_1 @ A ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_finset_1 @ B ) ) ) ))).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X4 : $i, X5 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.45          | (v1_finset_1 @ X4)
% 0.22/0.45          | ~ (v1_finset_1 @ X5))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc2_finset_1])).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (~ (v1_finset_1 @ X0) | (v1_finset_1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.45  thf(t16_finset_1, conjecture,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k6_subset_1 @ A @ B ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i]:
% 0.22/0.45        ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k6_subset_1 @ A @ B ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t16_finset_1])).
% 0.22/0.45  thf('5', plain, (~ (v1_finset_1 @ (k6_subset_1 @ sk_A @ sk_B))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.45  thf('7', plain, (~ (v1_finset_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain, (~ (v1_finset_1 @ sk_A)),
% 0.22/0.45      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.45  thf('9', plain, ((v1_finset_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('10', plain, ($false), inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
