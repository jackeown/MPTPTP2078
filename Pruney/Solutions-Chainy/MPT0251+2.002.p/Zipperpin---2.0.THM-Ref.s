%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.05V6ZU0OWY

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:01 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 135 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  475 ( 867 expanded)
%              Number of equality atoms :   59 ( 111 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('43',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('44',plain,
    ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('55',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.05V6ZU0OWY
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 1075 iterations in 0.250s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.70  thf(t46_zfmisc_1, conjecture,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( r2_hidden @ A @ B ) =>
% 0.50/0.70       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i,B:$i]:
% 0.50/0.70        ( ( r2_hidden @ A @ B ) =>
% 0.50/0.70          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.50/0.70  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t38_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.50/0.70       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.50/0.70         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 0.50/0.70          | ~ (r2_hidden @ X47 @ X48)
% 0.50/0.70          | ~ (r2_hidden @ X45 @ X48))),
% 0.50/0.70      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.50/0.70          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.50/0.70      inference('sup-', [status(thm)], ['0', '3'])).
% 0.50/0.70  thf(t69_enumset1, axiom,
% 0.50/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.70  thf('5', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.50/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.70  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.50/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.70  thf(t28_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (![X23 : $i, X24 : $i]:
% 0.50/0.70         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.70  thf('8', plain,
% 0.50/0.70      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.70  thf(t100_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      (![X20 : $i, X21 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ X20 @ X21)
% 0.50/0.70           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.50/0.70         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.50/0.70  thf(commutativity_k2_tarski, axiom,
% 0.50/0.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.50/0.70  thf('11', plain,
% 0.50/0.70      (![X31 : $i, X32 : $i]:
% 0.50/0.70         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 0.50/0.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.50/0.70  thf(l51_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.70  thf('12', plain,
% 0.50/0.70      (![X43 : $i, X44 : $i]:
% 0.50/0.70         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.50/0.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      (![X43 : $i, X44 : $i]:
% 0.50/0.70         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.50/0.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.70      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.70  thf(t1_boole, axiom,
% 0.50/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.70  thf('16', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.70  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.70  thf(t40_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (![X27 : $i, X28 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.50/0.70           = (k4_xboole_0 @ X27 @ X28))),
% 0.50/0.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf(d10_xboole_0, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.70  thf('20', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.70  thf('21', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.50/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (![X23 : $i, X24 : $i]:
% 0.50/0.70         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.70  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X20 : $i, X21 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ X20 @ X21)
% 0.50/0.70           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.70  thf('26', plain,
% 0.50/0.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['19', '25'])).
% 0.50/0.70  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.70  thf(t7_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.50/0.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      (![X23 : $i, X24 : $i]:
% 0.50/0.70         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.70  thf('31', plain,
% 0.50/0.70      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['27', '30'])).
% 0.50/0.70  thf('32', plain,
% 0.50/0.70      (![X20 : $i, X21 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ X20 @ X21)
% 0.50/0.70           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.70           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['31', '32'])).
% 0.50/0.70  thf('34', plain,
% 0.50/0.70      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.50/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      (![X43 : $i, X44 : $i]:
% 0.50/0.70         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.50/0.70      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.50/0.70  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.70  thf(t39_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (![X25 : $i, X26 : $i]:
% 0.50/0.70         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.50/0.70           = (k2_xboole_0 @ X25 @ X26))),
% 0.50/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['37', '38'])).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.50/0.70         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['36', '39'])).
% 0.50/0.70  thf('41', plain,
% 0.50/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.70  thf('42', plain,
% 0.50/0.70      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.50/0.70  thf('43', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.70  thf('44', plain, (((k3_tarski @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.70      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.70  thf('45', plain,
% 0.50/0.70      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.70      inference('demod', [status(thm)], ['40', '41', '44'])).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.70      inference('demod', [status(thm)], ['33', '45'])).
% 0.50/0.70  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.70      inference('demod', [status(thm)], ['26', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.50/0.70      inference('demod', [status(thm)], ['10', '47'])).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      (![X25 : $i, X26 : $i]:
% 0.50/0.70         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.50/0.70           = (k2_xboole_0 @ X25 @ X26))),
% 0.50/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.70  thf('50', plain,
% 0.50/0.70      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.50/0.70         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['48', '49'])).
% 0.50/0.70  thf('51', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.70  thf('52', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.50/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.50/0.70  thf('53', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('54', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.70      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.70  thf('55', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.50/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.50/0.70  thf('56', plain, ($false),
% 0.50/0.70      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
