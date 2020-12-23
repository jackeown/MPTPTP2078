%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fgPKo2gwkG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   74 (  83 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  554 ( 650 expanded)
%              Number of equality atoms :   51 (  60 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k5_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X10 @ X9 @ X8 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r2_hidden @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['29','32'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','28','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fgPKo2gwkG
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 305 iterations in 0.088s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(t48_zfmisc_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.36/0.54       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.54        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.36/0.54          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t71_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.54         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.36/0.54           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.54  thf(t70_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('3', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.54  thf(t72_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.36/0.54           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.36/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.54  thf(t60_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.54     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.36/0.54       ( k2_xboole_0 @
% 0.36/0.54         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.36/0.54           = (k2_xboole_0 @ (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 0.36/0.54              (k2_tarski @ X18 @ X19)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.36/0.54           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.54              (k2_tarski @ X5 @ X4)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf(t74_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.54     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.54       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.54         ((k5_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.36/0.54           = (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 0.36/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.36/0.54           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.54              (k2_tarski @ X5 @ X4)))),
% 0.36/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '10'])).
% 0.36/0.54  thf(t73_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.54         ((k4_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.36/0.54           = (k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 0.36/0.54      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.36/0.54           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.36/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.54           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.54         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.36/0.54           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.54  thf(t102_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X10 @ X9 @ X8) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf(l51_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X48 : $i, X49 : $i]:
% 0.36/0.54         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.36/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['17', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0))
% 0.36/0.54           = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['16', '21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_tarski @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 0.36/0.54           = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['15', '22'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(t41_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k2_tarski @ A @ B ) =
% 0.36/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         ((k2_tarski @ X11 @ X12)
% 0.36/0.54           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X48 : $i, X49 : $i]:
% 0.36/0.54         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.36/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('30', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t38_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.36/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X50 : $i, X52 : $i, X53 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_tarski @ X50 @ X52) @ X53)
% 0.36/0.54          | ~ (r2_hidden @ X52 @ X53)
% 0.36/0.54          | ~ (r2_hidden @ X50 @ X53))),
% 0.36/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.55          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.55  thf('33', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.55  thf(l32_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf(t39_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.36/0.55           = (k2_xboole_0 @ X6 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.36/0.55         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf(t1_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.55  thf('38', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain, (((sk_B) != (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '28', '39'])).
% 0.36/0.55  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
