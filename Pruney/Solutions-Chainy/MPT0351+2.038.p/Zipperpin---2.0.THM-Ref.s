%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.23suFeVrsk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:02 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   83 (  99 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  498 ( 652 expanded)
%              Number of equality atoms :   53 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X28 ) @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
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

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['21','38'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','45'])).

thf('47',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('49',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.23suFeVrsk
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 177 iterations in 0.063s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(dt_k2_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (![X28 : $i]: (m1_subset_1 @ (k2_subset_1 @ X28) @ (k1_zfmisc_1 @ X28))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.34/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.34/0.53  thf('1', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('2', plain, (![X28 : $i]: (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))),
% 0.34/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.34/0.53  thf(t28_subset_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i]:
% 0.34/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.34/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.34/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.34/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.34/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 0.34/0.53          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.34/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.34/0.53  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X31 : $i, X32 : $i]:
% 0.34/0.53         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 0.34/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.34/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_k3_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X29 : $i, X30 : $i]:
% 0.34/0.53         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 0.34/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf(d5_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X26 : $i, X27 : $i]:
% 0.34/0.53         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.34/0.53         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X26 : $i, X27 : $i]:
% 0.34/0.53         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.53  thf(t48_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.34/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.34/0.53         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.34/0.53         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup+', [status(thm)], ['14', '19'])).
% 0.34/0.53  thf('21', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup+', [status(thm)], ['9', '20'])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.34/0.53           = (k3_xboole_0 @ X8 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.34/0.53  thf(t36_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.34/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.34/0.53  thf(l32_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (![X1 : $i, X3 : $i]:
% 0.34/0.53         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.34/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.34/0.53  thf(t98_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         ((k2_xboole_0 @ X10 @ X11)
% 0.34/0.53           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.34/0.53           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.53  thf(t3_boole, axiom,
% 0.34/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.53  thf('29', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.34/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.34/0.53  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.34/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X1 : $i, X3 : $i]:
% 0.34/0.53         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.34/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.53  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         ((k2_xboole_0 @ X10 @ X11)
% 0.34/0.53           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.34/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.34/0.53  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.34/0.53  thf('37', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['28', '37'])).
% 0.34/0.53  thf('39', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['21', '38'])).
% 0.34/0.53  thf(commutativity_k2_tarski, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.34/0.53  thf(l51_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      (![X23 : $i, X24 : $i]:
% 0.34/0.53         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.34/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X23 : $i, X24 : $i]:
% 0.34/0.53         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.34/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.34/0.53  thf('45', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['39', '44'])).
% 0.34/0.53  thf('46', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['6', '45'])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.34/0.53         != (k2_subset_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('48', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('49', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('50', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.34/0.53  thf('51', plain, ($false),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['46', '50'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
