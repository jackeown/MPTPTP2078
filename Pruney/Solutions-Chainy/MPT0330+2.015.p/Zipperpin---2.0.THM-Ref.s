%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PQGVrA3s82

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:01 EST 2020

% Result     : Theorem 34.01s
% Output     : Refutation 34.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  437 ( 619 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ X20 @ ( k2_xboole_0 @ X17 @ X19 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X17 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      = ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X1 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_E ) @ sk_F ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_E ) @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_E ) @ ( k2_xboole_0 @ X0 @ sk_F ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) )
      = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['11','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PQGVrA3s82
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 34.01/34.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 34.01/34.25  % Solved by: fo/fo7.sh
% 34.01/34.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.01/34.25  % done 25066 iterations in 33.795s
% 34.01/34.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 34.01/34.25  % SZS output start Refutation
% 34.01/34.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 34.01/34.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.01/34.25  thf(sk_D_type, type, sk_D: $i).
% 34.01/34.25  thf(sk_E_type, type, sk_E: $i).
% 34.01/34.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 34.01/34.25  thf(sk_B_type, type, sk_B: $i).
% 34.01/34.25  thf(sk_A_type, type, sk_A: $i).
% 34.01/34.25  thf(sk_C_type, type, sk_C: $i).
% 34.01/34.25  thf(sk_F_type, type, sk_F: $i).
% 34.01/34.25  thf(t143_zfmisc_1, conjecture,
% 34.01/34.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 34.01/34.25     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 34.01/34.25         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 34.01/34.25       ( r1_tarski @
% 34.01/34.25         ( k2_xboole_0 @ A @ B ) @ 
% 34.01/34.25         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 34.01/34.25  thf(zf_stmt_0, negated_conjecture,
% 34.01/34.25    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 34.01/34.25        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 34.01/34.25            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 34.01/34.25          ( r1_tarski @
% 34.01/34.25            ( k2_xboole_0 @ A @ B ) @ 
% 34.01/34.25            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 34.01/34.25    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 34.01/34.25  thf('0', plain,
% 34.01/34.25      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 34.01/34.25          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 34.01/34.25           (k2_xboole_0 @ sk_D @ sk_F)))),
% 34.01/34.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.01/34.25  thf(t120_zfmisc_1, axiom,
% 34.01/34.25    (![A:$i,B:$i,C:$i]:
% 34.01/34.25     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 34.01/34.25         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 34.01/34.25       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 34.01/34.25         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 34.01/34.25  thf('1', plain,
% 34.01/34.25      (![X17 : $i, X19 : $i, X20 : $i]:
% 34.01/34.25         ((k2_zfmisc_1 @ X20 @ (k2_xboole_0 @ X17 @ X19))
% 34.01/34.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X20 @ X17) @ 
% 34.01/34.25              (k2_zfmisc_1 @ X20 @ X19)))),
% 34.01/34.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 34.01/34.25  thf(commutativity_k2_xboole_0, axiom,
% 34.01/34.25    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 34.01/34.25  thf('2', plain,
% 34.01/34.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.01/34.25      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 34.01/34.25  thf('3', plain,
% 34.01/34.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.01/34.25         ((k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X2 @ X1))
% 34.01/34.25           = (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 34.01/34.25      inference('sup+', [status(thm)], ['1', '2'])).
% 34.01/34.25  thf('4', plain,
% 34.01/34.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.01/34.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X17 @ X19) @ X18)
% 34.01/34.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 34.01/34.25              (k2_zfmisc_1 @ X19 @ X18)))),
% 34.01/34.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 34.01/34.25  thf('5', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 34.01/34.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.01/34.25  thf(t10_xboole_1, axiom,
% 34.01/34.25    (![A:$i,B:$i,C:$i]:
% 34.01/34.25     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 34.01/34.25  thf('6', plain,
% 34.01/34.25      (![X2 : $i, X3 : $i, X4 : $i]:
% 34.01/34.25         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 34.01/34.25      inference('cnf', [status(esa)], [t10_xboole_1])).
% 34.01/34.25  thf('7', plain,
% 34.01/34.25      (![X0 : $i]:
% 34.01/34.25         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 34.01/34.25      inference('sup-', [status(thm)], ['5', '6'])).
% 34.01/34.25  thf('8', plain,
% 34.01/34.25      (![X0 : $i]:
% 34.01/34.25         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F))),
% 34.01/34.25      inference('sup+', [status(thm)], ['4', '7'])).
% 34.01/34.25  thf(t9_xboole_1, axiom,
% 34.01/34.25    (![A:$i,B:$i,C:$i]:
% 34.01/34.25     ( ( r1_tarski @ A @ B ) =>
% 34.01/34.25       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 34.01/34.25  thf('9', plain,
% 34.01/34.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 34.01/34.25         (~ (r1_tarski @ X12 @ X13)
% 34.01/34.25          | (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ (k2_xboole_0 @ X13 @ X14)))),
% 34.01/34.25      inference('cnf', [status(esa)], [t9_xboole_1])).
% 34.01/34.25  thf('10', plain,
% 34.01/34.25      (![X0 : $i, X1 : $i]:
% 34.01/34.25         (r1_tarski @ (k2_xboole_0 @ sk_B @ X1) @ 
% 34.01/34.25          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_E) @ sk_F) @ X1))),
% 34.01/34.25      inference('sup-', [status(thm)], ['8', '9'])).
% 34.01/34.25  thf('11', plain,
% 34.01/34.25      (![X0 : $i, X1 : $i]:
% 34.01/34.25         (r1_tarski @ 
% 34.01/34.25          (k2_xboole_0 @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_E) @ X0)) @ 
% 34.01/34.25          (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_E) @ (k2_xboole_0 @ X0 @ sk_F)))),
% 34.01/34.25      inference('sup+', [status(thm)], ['3', '10'])).
% 34.01/34.25  thf('12', plain,
% 34.01/34.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.01/34.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X17 @ X19) @ X18)
% 34.01/34.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 34.01/34.25              (k2_zfmisc_1 @ X19 @ X18)))),
% 34.01/34.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 34.01/34.25  thf(t7_xboole_1, axiom,
% 34.01/34.25    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 34.01/34.25  thf('13', plain,
% 34.01/34.25      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 34.01/34.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 34.01/34.25  thf('14', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 34.01/34.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.01/34.25  thf(t12_xboole_1, axiom,
% 34.01/34.25    (![A:$i,B:$i]:
% 34.01/34.25     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 34.01/34.25  thf('15', plain,
% 34.01/34.25      (![X8 : $i, X9 : $i]:
% 34.01/34.25         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 34.01/34.25      inference('cnf', [status(esa)], [t12_xboole_1])).
% 34.01/34.25  thf('16', plain,
% 34.01/34.25      (((k2_xboole_0 @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 34.01/34.25         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 34.01/34.25      inference('sup-', [status(thm)], ['14', '15'])).
% 34.01/34.25  thf(t11_xboole_1, axiom,
% 34.01/34.25    (![A:$i,B:$i,C:$i]:
% 34.01/34.25     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 34.01/34.25  thf('17', plain,
% 34.01/34.25      (![X5 : $i, X6 : $i, X7 : $i]:
% 34.01/34.25         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 34.01/34.25      inference('cnf', [status(esa)], [t11_xboole_1])).
% 34.01/34.25  thf('18', plain,
% 34.01/34.25      (![X0 : $i]:
% 34.01/34.25         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0)
% 34.01/34.25          | (r1_tarski @ sk_A @ X0))),
% 34.01/34.25      inference('sup-', [status(thm)], ['16', '17'])).
% 34.01/34.25  thf('19', plain,
% 34.01/34.26      (![X0 : $i]:
% 34.01/34.26         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 34.01/34.26      inference('sup-', [status(thm)], ['13', '18'])).
% 34.01/34.26  thf('20', plain,
% 34.01/34.26      (![X0 : $i]:
% 34.01/34.26         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))),
% 34.01/34.26      inference('sup+', [status(thm)], ['12', '19'])).
% 34.01/34.26  thf('21', plain,
% 34.01/34.26      (![X8 : $i, X9 : $i]:
% 34.01/34.26         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 34.01/34.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 34.01/34.26  thf('22', plain,
% 34.01/34.26      (![X0 : $i]:
% 34.01/34.26         ((k2_xboole_0 @ sk_A @ 
% 34.01/34.26           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))
% 34.01/34.26           = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))),
% 34.01/34.26      inference('sup-', [status(thm)], ['20', '21'])).
% 34.01/34.26  thf('23', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.01/34.26      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 34.01/34.26  thf('24', plain,
% 34.01/34.26      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 34.01/34.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 34.01/34.26  thf('25', plain,
% 34.01/34.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 34.01/34.26         (~ (r1_tarski @ X12 @ X13)
% 34.01/34.26          | (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ (k2_xboole_0 @ X13 @ X14)))),
% 34.01/34.26      inference('cnf', [status(esa)], [t9_xboole_1])).
% 34.01/34.26  thf('26', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.01/34.26         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 34.01/34.26          (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 34.01/34.26      inference('sup-', [status(thm)], ['24', '25'])).
% 34.01/34.26  thf('27', plain,
% 34.01/34.26      (![X8 : $i, X9 : $i]:
% 34.01/34.26         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 34.01/34.26      inference('cnf', [status(esa)], [t12_xboole_1])).
% 34.01/34.26  thf('28', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.01/34.26         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 34.01/34.26           (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 34.01/34.26           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 34.01/34.26      inference('sup-', [status(thm)], ['26', '27'])).
% 34.01/34.26  thf('29', plain,
% 34.01/34.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 34.01/34.26         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 34.01/34.26      inference('cnf', [status(esa)], [t11_xboole_1])).
% 34.01/34.26  thf('30', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.01/34.26         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 34.01/34.26          | (r1_tarski @ (k2_xboole_0 @ X2 @ X0) @ X3))),
% 34.01/34.26      inference('sup-', [status(thm)], ['28', '29'])).
% 34.01/34.26  thf('31', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.01/34.26         (~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 34.01/34.26          | (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ X3))),
% 34.01/34.26      inference('sup-', [status(thm)], ['23', '30'])).
% 34.01/34.26  thf('32', plain,
% 34.01/34.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.01/34.26         (~ (r1_tarski @ 
% 34.01/34.26             (k2_xboole_0 @ X2 @ 
% 34.01/34.26              (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D)) @ 
% 34.01/34.26             X1)
% 34.01/34.26          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ X1))),
% 34.01/34.26      inference('sup-', [status(thm)], ['22', '31'])).
% 34.01/34.26  thf('33', plain,
% 34.01/34.26      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 34.01/34.26        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 34.01/34.26         (k2_xboole_0 @ sk_D @ sk_F)))),
% 34.01/34.26      inference('sup-', [status(thm)], ['11', '32'])).
% 34.01/34.26  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 34.01/34.26  
% 34.01/34.26  % SZS output end Refutation
% 34.01/34.26  
% 34.01/34.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
