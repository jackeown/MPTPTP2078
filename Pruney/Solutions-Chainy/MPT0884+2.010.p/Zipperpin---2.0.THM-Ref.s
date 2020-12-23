%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EEKQwWFvwb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:25 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  67 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  629 ( 717 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t44_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','15'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X18 @ X21 ) @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X18 @ X19 ) @ ( k4_tarski @ X18 @ X20 ) @ ( k4_tarski @ X21 @ X19 ) @ ( k4_tarski @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_mcart_1 @ X26 @ X27 @ X28 )
      = ( k4_tarski @ ( k4_tarski @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X22 @ X23 ) @ ( k1_tarski @ X25 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X25 ) @ ( k4_tarski @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['16','25','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EEKQwWFvwb
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 3.22/3.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.22/3.44  % Solved by: fo/fo7.sh
% 3.22/3.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.22/3.44  % done 4647 iterations in 3.003s
% 3.22/3.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.22/3.44  % SZS output start Refutation
% 3.22/3.44  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 3.22/3.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.22/3.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.22/3.44  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.22/3.44  thf(sk_B_type, type, sk_B: $i).
% 3.22/3.44  thf(sk_A_type, type, sk_A: $i).
% 3.22/3.44  thf(sk_E_type, type, sk_E: $i).
% 3.22/3.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.22/3.44  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 3.22/3.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.22/3.44  thf(sk_C_type, type, sk_C: $i).
% 3.22/3.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.22/3.44  thf(sk_D_type, type, sk_D: $i).
% 3.22/3.44  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.22/3.44  thf(t44_mcart_1, conjecture,
% 3.22/3.44    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.22/3.44     ( ( k3_zfmisc_1 @
% 3.22/3.44         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 3.22/3.44       ( k2_enumset1 @
% 3.22/3.44         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 3.22/3.44         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 3.22/3.44  thf(zf_stmt_0, negated_conjecture,
% 3.22/3.44    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.22/3.44        ( ( k3_zfmisc_1 @
% 3.22/3.44            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 3.22/3.44          ( k2_enumset1 @
% 3.22/3.44            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 3.22/3.44            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 3.22/3.44    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 3.22/3.44  thf('0', plain,
% 3.22/3.44      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 3.22/3.44         (k2_tarski @ sk_D @ sk_E))
% 3.22/3.44         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 3.22/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.22/3.44  thf(t70_enumset1, axiom,
% 3.22/3.44    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.22/3.44  thf('1', plain,
% 3.22/3.44      (![X11 : $i, X12 : $i]:
% 3.22/3.44         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 3.22/3.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.22/3.44  thf(commutativity_k2_tarski, axiom,
% 3.22/3.44    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.22/3.44  thf('2', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.22/3.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.22/3.44  thf('3', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i]:
% 3.22/3.44         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.22/3.44      inference('sup+', [status(thm)], ['1', '2'])).
% 3.22/3.44  thf('4', plain,
% 3.22/3.44      (![X11 : $i, X12 : $i]:
% 3.22/3.44         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 3.22/3.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.22/3.44  thf('5', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i]:
% 3.22/3.44         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.22/3.44      inference('sup+', [status(thm)], ['3', '4'])).
% 3.22/3.44  thf(t46_enumset1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.22/3.44     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.22/3.44       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.22/3.44  thf('6', plain,
% 3.22/3.44      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 3.22/3.44           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ (k1_tarski @ X9)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.22/3.44  thf('7', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 3.22/3.44           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.22/3.44      inference('sup+', [status(thm)], ['5', '6'])).
% 3.22/3.44  thf(t71_enumset1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i]:
% 3.22/3.44     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.22/3.44  thf('8', plain,
% 3.22/3.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 3.22/3.44           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 3.22/3.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.22/3.44  thf('9', plain,
% 3.22/3.44      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 3.22/3.44           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ (k1_tarski @ X9)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.22/3.44  thf('10', plain,
% 3.22/3.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 3.22/3.44           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 3.22/3.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.22/3.44  thf('11', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.44         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.22/3.44      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 3.22/3.44  thf(t44_enumset1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.22/3.44     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.22/3.44       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 3.22/3.44  thf('12', plain,
% 3.22/3.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 3.22/3.44           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X4 @ X5)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t44_enumset1])).
% 3.22/3.44  thf('13', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0)
% 3.22/3.44           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 3.22/3.44      inference('sup+', [status(thm)], ['11', '12'])).
% 3.22/3.44  thf('14', plain,
% 3.22/3.44      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 3.22/3.44           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X4 @ X5)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t44_enumset1])).
% 3.22/3.44  thf('15', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.22/3.44         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.22/3.44      inference('sup+', [status(thm)], ['13', '14'])).
% 3.22/3.44  thf('16', plain,
% 3.22/3.44      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 3.22/3.44         (k2_tarski @ sk_D @ sk_E))
% 3.22/3.44         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 3.22/3.44             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 3.22/3.44      inference('demod', [status(thm)], ['0', '15'])).
% 3.22/3.44  thf(d3_mcart_1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i]:
% 3.22/3.44     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 3.22/3.44  thf('17', plain,
% 3.22/3.44      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.22/3.44         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 3.22/3.44           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 3.22/3.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.22/3.44  thf('18', plain,
% 3.22/3.44      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.22/3.44         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 3.22/3.44           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 3.22/3.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.22/3.44  thf(t146_zfmisc_1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.22/3.44     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 3.22/3.44       ( k2_enumset1 @
% 3.22/3.44         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 3.22/3.44         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 3.22/3.44  thf('19', plain,
% 3.22/3.44      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ (k2_tarski @ X18 @ X21) @ (k2_tarski @ X19 @ X20))
% 3.22/3.44           = (k2_enumset1 @ (k4_tarski @ X18 @ X19) @ 
% 3.22/3.44              (k4_tarski @ X18 @ X20) @ (k4_tarski @ X21 @ X19) @ 
% 3.22/3.44              (k4_tarski @ X21 @ X20)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 3.22/3.44  thf('20', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 3.22/3.44           (k2_tarski @ X0 @ X3))
% 3.22/3.44           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 3.22/3.44              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 3.22/3.44              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 3.22/3.44      inference('sup+', [status(thm)], ['18', '19'])).
% 3.22/3.44  thf('21', plain,
% 3.22/3.44      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.22/3.44         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 3.22/3.44           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 3.22/3.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.22/3.44  thf('22', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 3.22/3.44           (k2_tarski @ X0 @ X3))
% 3.22/3.44           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 3.22/3.44              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 3.22/3.44              (k4_tarski @ X4 @ X3)))),
% 3.22/3.44      inference('demod', [status(thm)], ['20', '21'])).
% 3.22/3.44  thf('23', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ 
% 3.22/3.44           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 3.22/3.44           (k2_tarski @ X0 @ X3))
% 3.22/3.44           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 3.22/3.44              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 3.22/3.44              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 3.22/3.44      inference('sup+', [status(thm)], ['17', '22'])).
% 3.22/3.44  thf('24', plain,
% 3.22/3.44      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.22/3.44         ((k3_mcart_1 @ X26 @ X27 @ X28)
% 3.22/3.44           = (k4_tarski @ (k4_tarski @ X26 @ X27) @ X28))),
% 3.22/3.44      inference('cnf', [status(esa)], [d3_mcart_1])).
% 3.22/3.44  thf('25', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ 
% 3.22/3.44           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 3.22/3.44           (k2_tarski @ X0 @ X3))
% 3.22/3.44           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 3.22/3.44              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 3.22/3.44              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 3.22/3.44      inference('demod', [status(thm)], ['23', '24'])).
% 3.22/3.44  thf(t36_zfmisc_1, axiom,
% 3.22/3.44    (![A:$i,B:$i,C:$i]:
% 3.22/3.44     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 3.22/3.44         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 3.22/3.44       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 3.22/3.44         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 3.22/3.44  thf('26', plain,
% 3.22/3.44      (![X22 : $i, X23 : $i, X25 : $i]:
% 3.22/3.44         ((k2_zfmisc_1 @ (k2_tarski @ X22 @ X23) @ (k1_tarski @ X25))
% 3.22/3.44           = (k2_tarski @ (k4_tarski @ X22 @ X25) @ (k4_tarski @ X23 @ X25)))),
% 3.22/3.44      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.22/3.44  thf('27', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.22/3.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.22/3.44  thf('28', plain,
% 3.22/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.22/3.44         ((k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X2 @ X0))
% 3.22/3.44           = (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.22/3.45      inference('sup+', [status(thm)], ['26', '27'])).
% 3.22/3.45  thf('29', plain,
% 3.22/3.45      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.22/3.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.22/3.45  thf(d3_zfmisc_1, axiom,
% 3.22/3.45    (![A:$i,B:$i,C:$i]:
% 3.22/3.45     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 3.22/3.45       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 3.22/3.45  thf('30', plain,
% 3.22/3.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.22/3.45         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 3.22/3.45           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 3.22/3.45      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 3.22/3.45  thf('31', plain,
% 3.22/3.45      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 3.22/3.45         (k2_tarski @ sk_D @ sk_E))
% 3.22/3.45         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 3.22/3.45             (k2_tarski @ sk_D @ sk_E)))),
% 3.22/3.45      inference('demod', [status(thm)], ['16', '25', '28', '29', '30'])).
% 3.22/3.45  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 3.22/3.45  
% 3.22/3.45  % SZS output end Refutation
% 3.22/3.45  
% 3.22/3.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
