%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wvUFAiOAtQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 (  79 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  396 ( 459 expanded)
%              Number of equality atoms :   41 (  48 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ X48 )
      | ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X52: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ ( k3_tarski @ X43 ) )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X46: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('28',plain,(
    ! [X50: $i] :
      ( ( k2_subset_1 @ X50 )
      = X50 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ! [X50: $i] :
      ( ( k2_subset_1 @ X50 )
      = X50 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('30',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X51 ) @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('32',plain,(
    ! [X50: $i] :
      ( ( k2_subset_1 @ X50 )
      = X50 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X54 ) )
      | ( ( k4_subset_1 @ X54 @ X53 @ X55 )
        = ( k2_xboole_0 @ X53 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wvUFAiOAtQ
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 88 iterations in 0.041s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(t28_subset_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.20/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d2_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.46       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X47 : $i, X48 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X47 @ X48)
% 0.20/0.46          | (r2_hidden @ X47 @ X48)
% 0.20/0.46          | (v1_xboole_0 @ X48))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(fc1_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.46  thf('3', plain, (![X52 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X52))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.46  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(l49_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X42 : $i, X43 : $i]:
% 0.20/0.46         ((r1_tarski @ X42 @ (k3_tarski @ X43)) | ~ (r2_hidden @ X42 @ X43))),
% 0.20/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.46  thf('6', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(t99_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.46  thf('7', plain, (![X46 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X46)) = (X46))),
% 0.20/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.46  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf(t28_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.46  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.46  thf(t100_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.46           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.46  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf(t92_xboole_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('17', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.46  thf(t91_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.46       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.46           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.46           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.46  thf(t5_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.46  thf('21', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.46  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['16', '23'])).
% 0.20/0.46  thf(t98_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.46           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.46  thf('26', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.20/0.46         != (k2_subset_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.46  thf('28', plain, (![X50 : $i]: ((k2_subset_1 @ X50) = (X50))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.46  thf('29', plain, (![X50 : $i]: ((k2_subset_1 @ X50) = (X50))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.46  thf('30', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.46  thf(dt_k2_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X51 : $i]: (m1_subset_1 @ (k2_subset_1 @ X51) @ (k1_zfmisc_1 @ X51))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.46  thf('32', plain, (![X50 : $i]: ((k2_subset_1 @ X50) = (X50))),
% 0.20/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.46  thf('33', plain, (![X51 : $i]: (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X51))),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('34', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.20/0.46          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X54))
% 0.20/0.46          | ((k4_subset_1 @ X54 @ X53 @ X55) = (k2_xboole_0 @ X53 @ X55)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['33', '36'])).
% 0.20/0.46  thf('38', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['30', '37'])).
% 0.20/0.46  thf('39', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['26', '38'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
