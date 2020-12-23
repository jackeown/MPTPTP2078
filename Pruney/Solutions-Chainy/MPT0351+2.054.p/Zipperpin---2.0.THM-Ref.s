%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dDRxQqA5lX

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  483 ( 837 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X39 ) @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( k2_subset_1 @ X38 )
      = X38 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
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

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_subset_1 @ X36 @ X37 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k4_subset_1 @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k4_subset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k4_subset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( r1_tarski @ X48 @ X46 )
      | ( r2_hidden @ ( sk_D @ X46 @ X48 @ X47 ) @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('30',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( r1_tarski @ X48 @ X46 )
      | ~ ( r2_hidden @ ( sk_D @ X46 @ X48 @ X47 ) @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['27','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['18','39'])).

thf('41',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X38: $i] :
      ( ( k2_subset_1 @ X38 )
      = X38 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X38: $i] :
      ( ( k2_subset_1 @ X38 )
      = X38 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('46',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dDRxQqA5lX
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 63 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(dt_k2_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X39 : $i]: (m1_subset_1 @ (k2_subset_1 @ X39) @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.49  thf('1', plain, (![X38 : $i]: ((k2_subset_1 @ X38) = (X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.49  thf('2', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t28_subset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(commutativity_k4_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.21/0.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 0.21/0.49          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k4_subset_1 @ X36 @ X37 @ X35)))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k4_subset_1 @ sk_A @ X0 @ sk_B))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k4_subset_1 @ sk_A @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf('7', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.21/0.49          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 0.21/0.49          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((k2_xboole_0 @ sk_B @ sk_A) = (k4_subset_1 @ sk_A @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.49  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.21/0.49          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 0.21/0.49          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((k4_subset_1 @ sk_A @ sk_A @ sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '17'])).
% 0.21/0.49  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t7_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49           ( ( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.49                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.21/0.49          | (r1_tarski @ X48 @ X46)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X46 @ X48 @ X47) @ X48)
% 0.21/0.49          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.21/0.49          | (r1_tarski @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_A)
% 0.21/0.49        | (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l3_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X40 @ X41)
% 0.21/0.49          | (r2_hidden @ X40 @ X42)
% 0.21/0.49          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_A)
% 0.21/0.49        | (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.49  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, (![X39 : $i]: (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X39))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.21/0.49          | (r1_tarski @ X48 @ X46)
% 0.21/0.49          | ~ (r2_hidden @ (sk_D @ X46 @ X48 @ X47) @ X46)
% 0.21/0.49          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.49          | (r1_tarski @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_A)
% 0.21/0.49        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.49  thf('33', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['27', '32'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('35', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf(t22_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['35', '38'])).
% 0.21/0.49  thf('40', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['18', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.21/0.49         != (k2_subset_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, (![X38 : $i]: ((k2_subset_1 @ X38) = (X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.49  thf('43', plain, (![X38 : $i]: ((k2_subset_1 @ X38) = (X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.49  thf('44', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.49  thf('46', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['40', '46'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
