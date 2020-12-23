%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7pNVbN8uRK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:32 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 100 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  794 (1405 expanded)
%              Number of equality atoms :   60 ( 107 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ ( k2_xboole_0 @ X30 @ X32 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X30 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t132_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
        & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_zfmisc_1])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X30 @ X32 ) @ X31 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('36',plain,(
    ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['26','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7pNVbN8uRK
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 115 iterations in 0.281s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.73  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(t70_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      (![X8 : $i, X9 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf(t69_enumset1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.73  thf('1', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf(t71_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.54/0.73           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.54/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.73  thf(t72_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.73         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.54/0.73           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.54/0.73  thf(t73_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.54/0.73     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.54/0.73       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.73         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.54/0.73           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.54/0.73      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.54/0.73  thf(t61_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.73     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.54/0.73       ( k2_xboole_0 @
% 0.54/0.73         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.73         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.54/0.73           = (k2_xboole_0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.54/0.73              (k1_tarski @ X6)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.73         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.54/0.73           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.54/0.73              (k1_tarski @ X5)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf(t74_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.73     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.54/0.73       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.73         ((k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.54/0.73           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.54/0.73      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.54/0.73           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.54/0.73           = (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.54/0.73      inference('sup+', [status(thm)], ['4', '9'])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.73         ((k4_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.54/0.73           = (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.54/0.73      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.54/0.73           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.54/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.54/0.73           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.73      inference('sup+', [status(thm)], ['3', '12'])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.73         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.54/0.73           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.54/0.73           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 0.54/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.54/0.73           = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '15'])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.54/0.73           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.54/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.54/0.73           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.54/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf(t120_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.54/0.73         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.54/0.73       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.73         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X30 : $i, X32 : $i, X33 : $i]:
% 0.54/0.73         ((k2_zfmisc_1 @ X33 @ (k2_xboole_0 @ X30 @ X32))
% 0.54/0.73           = (k2_xboole_0 @ (k2_zfmisc_1 @ X33 @ X30) @ 
% 0.54/0.73              (k2_zfmisc_1 @ X33 @ X32)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.54/0.73  thf(t132_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.54/0.73         ( k2_xboole_0 @
% 0.54/0.73           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.54/0.73           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.54/0.73       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.54/0.73         ( k2_xboole_0 @
% 0.54/0.73           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.54/0.73           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.54/0.73            ( k2_xboole_0 @
% 0.54/0.73              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.54/0.73              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.54/0.73          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.54/0.73            ( k2_xboole_0 @
% 0.54/0.73              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.54/0.73              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.54/0.73        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.54/0.73      inference('split', [status(esa)], ['20'])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          != (k2_zfmisc_1 @ sk_C @ 
% 0.54/0.73              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          != (k2_zfmisc_1 @ sk_C @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['18', '22'])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X8 : $i, X9 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.54/0.73      inference('demod', [status(thm)], ['23', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (($false)
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 0.54/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.54/0.73           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.54/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.73         ((k2_zfmisc_1 @ (k2_xboole_0 @ X30 @ X32) @ X31)
% 0.54/0.73           = (k2_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 0.54/0.73              (k2_zfmisc_1 @ X32 @ X31)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.54/0.73      inference('split', [status(esa)], ['20'])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          != (k2_zfmisc_1 @ 
% 0.54/0.73              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          != (k2_zfmisc_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ sk_C)))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['27', '30'])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (![X8 : $i, X9 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.54/0.73         <= (~
% 0.54/0.73             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 0.54/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.54/0.73      inference('simplify', [status(thm)], ['33'])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (~
% 0.54/0.73       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 0.54/0.73       ~
% 0.54/0.73       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.54/0.73             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 0.54/0.73      inference('split', [status(esa)], ['20'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (~
% 0.54/0.73       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.54/0.73             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 0.54/0.73      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.54/0.73  thf('37', plain, ($false),
% 0.54/0.73      inference('simpl_trail', [status(thm)], ['26', '36'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
