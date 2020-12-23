%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FPzZc27Qeh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 191 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k1_tarski @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k1_zfmisc_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('3',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FPzZc27Qeh
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 19 iterations in 0.017s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t4_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.48  thf(t55_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.48       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (((X9) = (k1_xboole_0))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ X9)
% 0.20/0.48          | (m1_subset_1 @ (k1_tarski @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.48          | ((k1_zfmisc_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t61_setfam_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( m1_subset_1 @
% 0.20/0.48       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( m1_subset_1 @
% 0.20/0.48          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain, (((k1_zfmisc_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t80_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X7 : $i]: (r1_tarski @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.20/0.48  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.48  thf('7', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf(t14_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.48         ( ![D:$i]:
% 0.20/0.48           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.20/0.48             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.20/0.48       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.48          | ~ (r1_tarski @ X2 @ X1)
% 0.20/0.48          | ~ (r1_tarski @ X1 @ (sk_D @ X2 @ X1 @ X0))
% 0.20/0.48          | ((X1) = (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_xboole_0) = (k2_xboole_0 @ X0 @ X1))
% 0.20/0.48          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.20/0.48          | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.20/0.48          | ((k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.48  thf(t1_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('12', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.48  thf('15', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.48  thf(t49_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.48  thf('17', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
