%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tjoA0DqMgp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 (  91 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 557 expanded)
%              Number of equality atoms :   38 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X44 ) @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k4_subset_1 @ X49 @ X48 @ X50 )
        = ( k2_xboole_0 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('32',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','27','30','31'])).

thf('33',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','32'])).

thf('34',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tjoA0DqMgp
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 43 iterations in 0.023s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(dt_k2_subset_1, axiom,
% 0.20/0.45    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X44 : $i]: (m1_subset_1 @ (k2_subset_1 @ X44) @ (k1_zfmisc_1 @ X44))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.45  thf('1', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.20/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.45  thf('2', plain, (![X44 : $i]: (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X44))),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t28_subset_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.20/0.45  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 0.20/0.45          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X49))
% 0.20/0.45          | ((k4_subset_1 @ X49 @ X48 @ X50) = (k2_xboole_0 @ X48 @ X50)))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.45  thf(d3_tarski, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X1 : $i, X3 : $i]:
% 0.20/0.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.45  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(l3_subset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X45 @ X46)
% 0.20/0.45          | (r2_hidden @ X45 @ X47)
% 0.20/0.45          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.20/0.45      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X1 : $i, X3 : $i]:
% 0.20/0.45         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.45  thf('13', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.45      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.45  thf(t28_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i]:
% 0.20/0.45         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.45  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf(t100_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.45           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.45      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf(t92_xboole_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.45  thf('19', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.45  thf('20', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf(t39_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i]:
% 0.20/0.45         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.20/0.45           = (k2_xboole_0 @ X9 @ X10))),
% 0.20/0.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.45      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf(commutativity_k2_tarski, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (![X12 : $i, X13 : $i]:
% 0.20/0.45         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.45  thf(l51_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (![X41 : $i, X42 : $i]:
% 0.20/0.45         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.20/0.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.45  thf('25', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      (![X41 : $i, X42 : $i]:
% 0.20/0.45         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.20/0.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.45  thf(t1_boole, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.45  thf('29', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.45  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.45  thf('32', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['22', '27', '30', '31'])).
% 0.20/0.45  thf('33', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['6', '32'])).
% 0.20/0.45  thf('34', plain,
% 0.20/0.45      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.20/0.45         != (k2_subset_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('35', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.20/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.45  thf('36', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.20/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.45  thf('37', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.45  thf('38', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['33', '37'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
