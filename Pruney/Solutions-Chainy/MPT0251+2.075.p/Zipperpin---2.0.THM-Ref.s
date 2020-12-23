%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WayIyHzIQk

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 101 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  450 ( 679 expanded)
%              Number of equality atoms :   38 (  63 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X23: $i] :
      ( ( k2_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) )
 != sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('43',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WayIyHzIQk
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 163 iterations in 0.071s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X3 : $i, X5 : $i]:
% 0.22/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf(t46_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.53          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.22/0.53  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(l1_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X44 : $i, X46 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.22/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.53  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf(t28_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf(t100_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X21 @ X22)
% 0.22/0.53           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.22/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf(t1_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.22/0.53       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.53         ((r2_hidden @ X6 @ X7)
% 0.22/0.53          | (r2_hidden @ X6 @ X8)
% 0.22/0.53          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.53          | (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.53          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.22/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X6 @ X7)
% 0.22/0.53          | ~ (r2_hidden @ X6 @ X8)
% 0.22/0.53          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.22/0.53      inference('clc', [status(thm)], ['10', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '15'])).
% 0.22/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.53  thf(l51_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.22/0.53           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.53  thf(t1_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.53  thf('21', plain, (![X23 : $i]: ((k2_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X23 : $i]: ((k3_tarski @ (k2_tarski @ X23 @ k1_xboole_0)) = (X23))),
% 0.22/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['20', '23'])).
% 0.22/0.53  thf(t7_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X32 : $i, X33 : $i]:
% 0.22/0.53         (r1_tarski @ X32 @ (k3_tarski @ (k2_tarski @ X32 @ X33)))),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.53      inference('sup+', [status(thm)], ['24', '27'])).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X18 : $i, X20 : $i]:
% 0.22/0.53         (((X18) = (X20))
% 0.22/0.53          | ~ (r1_tarski @ X20 @ X18)
% 0.22/0.53          | ~ (r1_tarski @ X18 @ X20))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '30'])).
% 0.22/0.53  thf(t39_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26))
% 0.22/0.53           = (k2_xboole_0 @ X26 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X26 @ (k4_xboole_0 @ X27 @ X26)))
% 0.22/0.53           = (k3_tarski @ (k2_tarski @ X26 @ X27)))),
% 0.22/0.53      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (((k3_tarski @ (k2_tarski @ sk_B @ k1_xboole_0))
% 0.22/0.53         = (k3_tarski @ (k2_tarski @ sk_B @ (k1_tarski @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['31', '35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (![X23 : $i]: ((k3_tarski @ (k2_tarski @ X23 @ k1_xboole_0)) = (X23))),
% 0.22/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k1_tarski @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.53  thf('39', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.22/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) != (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.22/0.53           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (((k3_tarski @ (k2_tarski @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf('44', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
