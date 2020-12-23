%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kXbA4sUxzj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:00 EST 2020

% Result     : Theorem 51.39s
% Output     : Refutation 51.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  73 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  381 ( 647 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ X28 @ ( k2_xboole_0 @ X25 @ X27 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X25 ) @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_E ) @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_E ) @ sk_F ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['7','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kXbA4sUxzj
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 51.39/51.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.39/51.63  % Solved by: fo/fo7.sh
% 51.39/51.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.39/51.63  % done 26574 iterations in 51.184s
% 51.39/51.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.39/51.63  % SZS output start Refutation
% 51.39/51.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.39/51.63  thf(sk_F_type, type, sk_F: $i).
% 51.39/51.63  thf(sk_D_type, type, sk_D: $i).
% 51.39/51.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 51.39/51.63  thf(sk_B_type, type, sk_B: $i).
% 51.39/51.63  thf(sk_C_type, type, sk_C: $i).
% 51.39/51.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.39/51.63  thf(sk_A_type, type, sk_A: $i).
% 51.39/51.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 51.39/51.63  thf(sk_E_type, type, sk_E: $i).
% 51.39/51.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.39/51.63  thf(t143_zfmisc_1, conjecture,
% 51.39/51.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 51.39/51.63     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 51.39/51.63         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 51.39/51.63       ( r1_tarski @
% 51.39/51.63         ( k2_xboole_0 @ A @ B ) @ 
% 51.39/51.63         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 51.39/51.63  thf(zf_stmt_0, negated_conjecture,
% 51.39/51.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 51.39/51.63        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 51.39/51.63            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 51.39/51.63          ( r1_tarski @
% 51.39/51.63            ( k2_xboole_0 @ A @ B ) @ 
% 51.39/51.63            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 51.39/51.63    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 51.39/51.63  thf('0', plain,
% 51.39/51.63      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 51.39/51.63          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 51.39/51.63           (k2_xboole_0 @ sk_D @ sk_F)))),
% 51.39/51.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.39/51.63  thf(t120_zfmisc_1, axiom,
% 51.39/51.63    (![A:$i,B:$i,C:$i]:
% 51.39/51.63     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 51.39/51.63         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 51.39/51.63       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 51.39/51.63         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 51.39/51.63  thf('1', plain,
% 51.39/51.63      (![X25 : $i, X27 : $i, X28 : $i]:
% 51.39/51.63         ((k2_zfmisc_1 @ X28 @ (k2_xboole_0 @ X25 @ X27))
% 51.39/51.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ X28 @ X25) @ 
% 51.39/51.63              (k2_zfmisc_1 @ X28 @ X27)))),
% 51.39/51.63      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 51.39/51.63  thf(commutativity_k2_tarski, axiom,
% 51.39/51.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 51.39/51.63  thf('2', plain,
% 51.39/51.63      (![X19 : $i, X20 : $i]:
% 51.39/51.63         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 51.39/51.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 51.39/51.63  thf(l51_zfmisc_1, axiom,
% 51.39/51.63    (![A:$i,B:$i]:
% 51.39/51.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 51.39/51.63  thf('3', plain,
% 51.39/51.63      (![X23 : $i, X24 : $i]:
% 51.39/51.63         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 51.39/51.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.39/51.63  thf('4', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]:
% 51.39/51.63         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 51.39/51.63      inference('sup+', [status(thm)], ['2', '3'])).
% 51.39/51.63  thf('5', plain,
% 51.39/51.63      (![X23 : $i, X24 : $i]:
% 51.39/51.63         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 51.39/51.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.39/51.63  thf('6', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.39/51.63      inference('sup+', [status(thm)], ['4', '5'])).
% 51.39/51.63  thf('7', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.39/51.63         ((k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 51.39/51.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 51.39/51.63      inference('sup+', [status(thm)], ['1', '6'])).
% 51.39/51.63  thf('8', plain,
% 51.39/51.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 51.39/51.63         ((k2_zfmisc_1 @ (k2_xboole_0 @ X25 @ X27) @ X26)
% 51.39/51.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 51.39/51.63              (k2_zfmisc_1 @ X27 @ X26)))),
% 51.39/51.63      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 51.39/51.63  thf(t7_xboole_1, axiom,
% 51.39/51.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 51.39/51.63  thf('9', plain,
% 51.39/51.63      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 51.39/51.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.39/51.63  thf('10', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 51.39/51.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.39/51.63  thf(t1_xboole_1, axiom,
% 51.39/51.63    (![A:$i,B:$i,C:$i]:
% 51.39/51.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 51.39/51.63       ( r1_tarski @ A @ C ) ))).
% 51.39/51.63  thf('11', plain,
% 51.39/51.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 51.39/51.63         (~ (r1_tarski @ X12 @ X13)
% 51.39/51.63          | ~ (r1_tarski @ X13 @ X14)
% 51.39/51.63          | (r1_tarski @ X12 @ X14))),
% 51.39/51.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.39/51.63  thf('12', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         ((r1_tarski @ sk_A @ X0)
% 51.39/51.63          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 51.39/51.63      inference('sup-', [status(thm)], ['10', '11'])).
% 51.39/51.63  thf('13', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 51.39/51.63      inference('sup-', [status(thm)], ['9', '12'])).
% 51.39/51.63  thf('14', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))),
% 51.39/51.63      inference('sup+', [status(thm)], ['8', '13'])).
% 51.39/51.63  thf('15', plain,
% 51.39/51.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 51.39/51.63         ((k2_zfmisc_1 @ (k2_xboole_0 @ X25 @ X27) @ X26)
% 51.39/51.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 51.39/51.63              (k2_zfmisc_1 @ X27 @ X26)))),
% 51.39/51.63      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 51.39/51.63  thf('16', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.39/51.63      inference('sup+', [status(thm)], ['4', '5'])).
% 51.39/51.63  thf('17', plain,
% 51.39/51.63      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 51.39/51.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.39/51.63  thf('18', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 51.39/51.63      inference('sup+', [status(thm)], ['16', '17'])).
% 51.39/51.63  thf('19', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 51.39/51.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.39/51.63  thf('20', plain,
% 51.39/51.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 51.39/51.63         (~ (r1_tarski @ X12 @ X13)
% 51.39/51.63          | ~ (r1_tarski @ X13 @ X14)
% 51.39/51.63          | (r1_tarski @ X12 @ X14))),
% 51.39/51.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.39/51.63  thf('21', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         ((r1_tarski @ sk_B @ X0)
% 51.39/51.63          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 51.39/51.63      inference('sup-', [status(thm)], ['19', '20'])).
% 51.39/51.63  thf('22', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 51.39/51.63      inference('sup-', [status(thm)], ['18', '21'])).
% 51.39/51.63  thf('23', plain,
% 51.39/51.63      (![X0 : $i]:
% 51.39/51.63         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F))),
% 51.39/51.63      inference('sup+', [status(thm)], ['15', '22'])).
% 51.39/51.63  thf(t13_xboole_1, axiom,
% 51.39/51.63    (![A:$i,B:$i,C:$i,D:$i]:
% 51.39/51.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 51.39/51.63       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 51.39/51.63  thf('24', plain,
% 51.39/51.63      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 51.39/51.63         (~ (r1_tarski @ X8 @ X9)
% 51.39/51.63          | ~ (r1_tarski @ X10 @ X11)
% 51.39/51.63          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 51.39/51.63      inference('cnf', [status(esa)], [t13_xboole_1])).
% 51.39/51.63  thf('25', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.39/51.63         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X2) @ 
% 51.39/51.63           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F) @ X1))
% 51.39/51.63          | ~ (r1_tarski @ X2 @ X1))),
% 51.39/51.63      inference('sup-', [status(thm)], ['23', '24'])).
% 51.39/51.63  thf('26', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]:
% 51.39/51.63         (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 51.39/51.63          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_E) @ sk_F) @ 
% 51.39/51.63           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D)))),
% 51.39/51.63      inference('sup-', [status(thm)], ['14', '25'])).
% 51.39/51.63  thf('27', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.39/51.63      inference('sup+', [status(thm)], ['4', '5'])).
% 51.39/51.63  thf('28', plain,
% 51.39/51.63      (![X0 : $i, X1 : $i]:
% 51.39/51.63         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 51.39/51.63          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_E) @ sk_F) @ 
% 51.39/51.63           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D)))),
% 51.39/51.63      inference('demod', [status(thm)], ['26', '27'])).
% 51.39/51.63  thf('29', plain,
% 51.39/51.63      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 51.39/51.63        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 51.39/51.63         (k2_xboole_0 @ sk_D @ sk_F)))),
% 51.39/51.63      inference('sup+', [status(thm)], ['7', '28'])).
% 51.39/51.63  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 51.39/51.63  
% 51.39/51.63  % SZS output end Refutation
% 51.39/51.63  
% 51.39/51.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
