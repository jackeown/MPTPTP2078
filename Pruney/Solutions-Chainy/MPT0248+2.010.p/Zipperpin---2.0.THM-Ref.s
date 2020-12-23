%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.desYJr672m

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:19 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 257 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  536 (3165 expanded)
%              Number of equality atoms :  110 ( 706 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('21',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( sk_C
       != ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C ) )
   <= ( ( sk_C
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( sk_C
       != ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ X0 ) ) )
   <= ( ( sk_C
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('43',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('44',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('47',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['41','45','46','47'])).

thf('49',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','48'])).

thf('50',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['41','45','46','54'])).

thf('56',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','49','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.desYJr672m
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:46:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 205 iterations in 0.065s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(commutativity_k2_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.23/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.23/0.54  thf(l51_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]:
% 0.23/0.54         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]:
% 0.23/0.54         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.23/0.54  thf(t46_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X4 : $i, X5 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.23/0.54  thf(l32_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.54          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['4', '8'])).
% 0.23/0.54  thf(t43_zfmisc_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.54          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.54          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.54          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.54        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.54             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.54             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.54             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.23/0.54  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(l3_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.23/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i]:
% 0.23/0.54         (((X12) = (k1_tarski @ X11))
% 0.23/0.54          | ((X12) = (k1_xboole_0))
% 0.23/0.54          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.23/0.54          | ((X0) = (k1_xboole_0))
% 0.23/0.54          | ((X0) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.54  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.23/0.54          | ((X0) = (k1_xboole_0))
% 0.23/0.54          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.23/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      ((((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '14'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.23/0.54      inference('split', [status(esa)], ['16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.23/0.54          | ((X0) = (k1_xboole_0))
% 0.23/0.54          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.23/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['16'])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.23/0.54         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.23/0.54         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.54  thf(t1_boole, axiom,
% 0.23/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.54  thf('27', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.23/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (![X4 : $i, X5 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.23/0.54  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_B)))
% 0.23/0.54         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup+', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['32'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.23/0.54         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['31', '33'])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      ((![X0 : $i]: ((sk_C) != (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C)))
% 0.23/0.54         <= (~ (((sk_C) = (k1_tarski @ sk_A))) & 
% 0.23/0.54             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '34'])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      ((![X0 : $i]: ((sk_C) != (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ X0))))
% 0.23/0.54         <= (~ (((sk_C) = (k1_tarski @ sk_A))) & 
% 0.23/0.54             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '35'])).
% 0.23/0.54  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('38', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.23/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.23/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      ((((sk_C) != (sk_C)))
% 0.23/0.54         <= (~ (((sk_C) = (k1_tarski @ sk_A))) & 
% 0.23/0.54             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['36', '39'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      ((((sk_B) = (k1_tarski @ sk_A))) | (((sk_C) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.23/0.54      inference('split', [status(esa)], ['32'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      ((((sk_B) != (sk_B)))
% 0.23/0.54         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.54  thf('45', plain,
% 0.23/0.54      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.23/0.54  thf('46', plain,
% 0.23/0.54      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.23/0.54      inference('split', [status(esa)], ['32'])).
% 0.23/0.54  thf('47', plain,
% 0.23/0.54      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['16'])).
% 0.23/0.54  thf('48', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['41', '45', '46', '47'])).
% 0.23/0.54  thf('49', plain, (((sk_C) != (k1_xboole_0))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['17', '48'])).
% 0.23/0.54  thf('50', plain,
% 0.23/0.54      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['32'])).
% 0.23/0.54  thf('51', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.23/0.54         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.23/0.54  thf('53', plain,
% 0.23/0.54      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('54', plain,
% 0.23/0.54      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['53'])).
% 0.23/0.54  thf('55', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['41', '45', '46', '54'])).
% 0.23/0.54  thf('56', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['52', '55'])).
% 0.23/0.54  thf('57', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['15', '49', '56'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
