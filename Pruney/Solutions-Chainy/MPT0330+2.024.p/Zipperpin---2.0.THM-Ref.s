%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TNEnJD0Br1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:02 EST 2020

% Result     : Theorem 4.05s
% Output     : Refutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 110 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  466 ( 978 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_E ) @ ( k2_xboole_0 @ sk_D_1 @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ X29 @ ( k2_xboole_0 @ X26 @ X28 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X26 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X26 @ X28 ) @ X27 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X1 ) @ ( k2_xboole_0 @ sk_F @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ X29 @ ( k2_xboole_0 @ X26 @ X28 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X26 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X26 @ X28 ) @ X27 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C_1 ) @ ( k2_xboole_0 @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( r1_tarski @ ( k2_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('39',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_E ) @ ( k2_xboole_0 @ sk_D_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TNEnJD0Br1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.05/4.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.05/4.27  % Solved by: fo/fo7.sh
% 4.05/4.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.05/4.27  % done 4638 iterations in 3.821s
% 4.05/4.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.05/4.27  % SZS output start Refutation
% 4.05/4.27  thf(sk_A_type, type, sk_A: $i).
% 4.05/4.27  thf(sk_B_type, type, sk_B: $i).
% 4.05/4.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.05/4.27  thf(sk_F_type, type, sk_F: $i).
% 4.05/4.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.05/4.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.05/4.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.05/4.27  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.05/4.27  thf(sk_E_type, type, sk_E: $i).
% 4.05/4.27  thf(t143_zfmisc_1, conjecture,
% 4.05/4.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.05/4.27     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 4.05/4.27         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 4.05/4.27       ( r1_tarski @
% 4.05/4.27         ( k2_xboole_0 @ A @ B ) @ 
% 4.05/4.27         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 4.05/4.27  thf(zf_stmt_0, negated_conjecture,
% 4.05/4.27    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.05/4.27        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 4.05/4.27            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 4.05/4.27          ( r1_tarski @
% 4.05/4.27            ( k2_xboole_0 @ A @ B ) @ 
% 4.05/4.27            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 4.05/4.27    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 4.05/4.27  thf('0', plain,
% 4.05/4.27      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 4.05/4.27          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_E) @ 
% 4.05/4.27           (k2_xboole_0 @ sk_D_1 @ sk_F)))),
% 4.05/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.05/4.27  thf(t120_zfmisc_1, axiom,
% 4.05/4.27    (![A:$i,B:$i,C:$i]:
% 4.05/4.27     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 4.05/4.27         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 4.05/4.27       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.05/4.27         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 4.05/4.27  thf('1', plain,
% 4.05/4.27      (![X26 : $i, X28 : $i, X29 : $i]:
% 4.05/4.27         ((k2_zfmisc_1 @ X29 @ (k2_xboole_0 @ X26 @ X28))
% 4.05/4.27           = (k2_xboole_0 @ (k2_zfmisc_1 @ X29 @ X26) @ 
% 4.05/4.27              (k2_zfmisc_1 @ X29 @ X28)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.05/4.27  thf(t7_xboole_1, axiom,
% 4.05/4.27    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.05/4.27  thf('2', plain,
% 4.05/4.27      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 4.05/4.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.05/4.27  thf('3', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.05/4.27         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 4.05/4.27          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.05/4.27      inference('sup+', [status(thm)], ['1', '2'])).
% 4.05/4.27  thf('4', plain,
% 4.05/4.27      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.05/4.27         ((k2_zfmisc_1 @ (k2_xboole_0 @ X26 @ X28) @ X27)
% 4.05/4.27           = (k2_xboole_0 @ (k2_zfmisc_1 @ X26 @ X27) @ 
% 4.05/4.27              (k2_zfmisc_1 @ X28 @ X27)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.05/4.27  thf('5', plain,
% 4.05/4.27      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 4.05/4.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.05/4.27  thf('6', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.05/4.27         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 4.05/4.27          (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 4.05/4.27      inference('sup+', [status(thm)], ['4', '5'])).
% 4.05/4.27  thf('7', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 4.05/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.05/4.27  thf(t1_xboole_1, axiom,
% 4.05/4.27    (![A:$i,B:$i,C:$i]:
% 4.05/4.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.05/4.27       ( r1_tarski @ A @ C ) ))).
% 4.05/4.27  thf('8', plain,
% 4.05/4.27      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X16 @ X17)
% 4.05/4.27          | ~ (r1_tarski @ X17 @ X18)
% 4.05/4.27          | (r1_tarski @ X16 @ X18))),
% 4.05/4.27      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.05/4.27  thf('9', plain,
% 4.05/4.27      (![X0 : $i]:
% 4.05/4.27         ((r1_tarski @ sk_B @ X0)
% 4.05/4.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 4.05/4.27      inference('sup-', [status(thm)], ['7', '8'])).
% 4.05/4.27  thf('10', plain,
% 4.05/4.27      (![X0 : $i]:
% 4.05/4.27         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 4.05/4.27      inference('sup-', [status(thm)], ['6', '9'])).
% 4.05/4.27  thf('11', plain,
% 4.05/4.27      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X16 @ X17)
% 4.05/4.27          | ~ (r1_tarski @ X17 @ X18)
% 4.05/4.27          | (r1_tarski @ X16 @ X18))),
% 4.05/4.27      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.05/4.27  thf('12', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         ((r1_tarski @ sk_B @ X1)
% 4.05/4.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F) @ 
% 4.05/4.27               X1))),
% 4.05/4.27      inference('sup-', [status(thm)], ['10', '11'])).
% 4.05/4.27  thf('13', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (r1_tarski @ sk_B @ 
% 4.05/4.27          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X1) @ (k2_xboole_0 @ sk_F @ X0)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['3', '12'])).
% 4.05/4.27  thf('14', plain,
% 4.05/4.27      (![X26 : $i, X28 : $i, X29 : $i]:
% 4.05/4.27         ((k2_zfmisc_1 @ X29 @ (k2_xboole_0 @ X26 @ X28))
% 4.05/4.27           = (k2_xboole_0 @ (k2_zfmisc_1 @ X29 @ X26) @ 
% 4.05/4.27              (k2_zfmisc_1 @ X29 @ X28)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.05/4.27  thf('15', plain,
% 4.05/4.27      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.05/4.27         ((k2_zfmisc_1 @ (k2_xboole_0 @ X26 @ X28) @ X27)
% 4.05/4.27           = (k2_xboole_0 @ (k2_zfmisc_1 @ X26 @ X27) @ 
% 4.05/4.27              (k2_zfmisc_1 @ X28 @ X27)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.05/4.27  thf('16', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 4.05/4.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.05/4.27  thf(t10_xboole_1, axiom,
% 4.05/4.27    (![A:$i,B:$i,C:$i]:
% 4.05/4.27     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.05/4.27  thf('17', plain,
% 4.05/4.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X13 @ X14)
% 4.05/4.27          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.05/4.27  thf('18', plain,
% 4.05/4.27      (![X0 : $i]:
% 4.05/4.27         (r1_tarski @ sk_A @ 
% 4.05/4.27          (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['16', '17'])).
% 4.05/4.27  thf('19', plain,
% 4.05/4.27      (![X0 : $i]:
% 4.05/4.27         (r1_tarski @ sk_A @ 
% 4.05/4.27          (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C_1) @ sk_D_1))),
% 4.05/4.27      inference('sup+', [status(thm)], ['15', '18'])).
% 4.05/4.27  thf('20', plain,
% 4.05/4.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X13 @ X14)
% 4.05/4.27          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.05/4.27  thf('21', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (r1_tarski @ sk_A @ 
% 4.05/4.27          (k2_xboole_0 @ X1 @ 
% 4.05/4.27           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C_1) @ sk_D_1)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['19', '20'])).
% 4.05/4.27  thf('22', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (r1_tarski @ sk_A @ 
% 4.05/4.27          (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C_1) @ 
% 4.05/4.27           (k2_xboole_0 @ X0 @ sk_D_1)))),
% 4.05/4.27      inference('sup+', [status(thm)], ['14', '21'])).
% 4.05/4.27  thf(t8_xboole_1, axiom,
% 4.05/4.27    (![A:$i,B:$i,C:$i]:
% 4.05/4.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.05/4.27       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.05/4.27  thf('23', plain,
% 4.05/4.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X21 @ X22)
% 4.05/4.27          | ~ (r1_tarski @ X23 @ X22)
% 4.05/4.27          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 4.05/4.27      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.05/4.27  thf('24', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.05/4.27         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 4.05/4.27           (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C_1) @ 
% 4.05/4.27            (k2_xboole_0 @ X0 @ sk_D_1)))
% 4.05/4.27          | ~ (r1_tarski @ X2 @ 
% 4.05/4.27               (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C_1) @ 
% 4.05/4.27                (k2_xboole_0 @ X0 @ sk_D_1))))),
% 4.05/4.27      inference('sup-', [status(thm)], ['22', '23'])).
% 4.05/4.27  thf('25', plain,
% 4.05/4.27      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 4.05/4.27        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C_1) @ 
% 4.05/4.27         (k2_xboole_0 @ sk_F @ sk_D_1)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['13', '24'])).
% 4.05/4.27  thf('26', plain,
% 4.05/4.27      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 4.05/4.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.05/4.27  thf(d10_xboole_0, axiom,
% 4.05/4.27    (![A:$i,B:$i]:
% 4.05/4.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.05/4.27  thf('27', plain,
% 4.05/4.27      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 4.05/4.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.05/4.27  thf('28', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 4.05/4.27      inference('simplify', [status(thm)], ['27'])).
% 4.05/4.27  thf('29', plain,
% 4.05/4.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X13 @ X14)
% 4.05/4.27          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 4.05/4.27      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.05/4.27  thf('30', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.05/4.27      inference('sup-', [status(thm)], ['28', '29'])).
% 4.05/4.27  thf('31', plain,
% 4.05/4.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.05/4.27         (~ (r1_tarski @ X21 @ X22)
% 4.05/4.27          | ~ (r1_tarski @ X23 @ X22)
% 4.05/4.27          | (r1_tarski @ (k2_xboole_0 @ X21 @ X23) @ X22))),
% 4.05/4.27      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.05/4.27  thf('32', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.05/4.27         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 4.05/4.27          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['30', '31'])).
% 4.05/4.27  thf('33', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 4.05/4.27      inference('sup-', [status(thm)], ['26', '32'])).
% 4.05/4.27  thf('34', plain,
% 4.05/4.27      (![X10 : $i, X12 : $i]:
% 4.05/4.27         (((X10) = (X12))
% 4.05/4.27          | ~ (r1_tarski @ X12 @ X10)
% 4.05/4.27          | ~ (r1_tarski @ X10 @ X12))),
% 4.05/4.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.05/4.27  thf('35', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 4.05/4.27          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 4.05/4.27      inference('sup-', [status(thm)], ['33', '34'])).
% 4.05/4.27  thf('36', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]:
% 4.05/4.27         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 4.05/4.27      inference('sup-', [status(thm)], ['26', '32'])).
% 4.05/4.27  thf('37', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.05/4.27      inference('demod', [status(thm)], ['35', '36'])).
% 4.05/4.27  thf('38', plain,
% 4.05/4.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.05/4.27      inference('demod', [status(thm)], ['35', '36'])).
% 4.05/4.27  thf('39', plain,
% 4.05/4.27      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 4.05/4.27        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_E) @ 
% 4.05/4.27         (k2_xboole_0 @ sk_D_1 @ sk_F)))),
% 4.05/4.27      inference('demod', [status(thm)], ['25', '37', '38'])).
% 4.05/4.27  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 4.05/4.27  
% 4.05/4.27  % SZS output end Refutation
% 4.05/4.27  
% 4.05/4.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
