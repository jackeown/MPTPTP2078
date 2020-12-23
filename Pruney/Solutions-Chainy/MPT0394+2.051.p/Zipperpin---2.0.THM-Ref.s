%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ax5aCo4Wt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 143 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  460 (1247 expanded)
%              Number of equality atoms :   47 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X31 ) @ ( k1_setfam_1 @ X32 ) ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) )
      | ( X29 != X30 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('22',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('39',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ax5aCo4Wt
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 677 iterations in 0.231s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(t70_enumset1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (![X22 : $i, X23 : $i]:
% 0.46/0.68         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.68  thf(t69_enumset1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.68  thf('1', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['0', '1'])).
% 0.46/0.68  thf(t46_enumset1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.46/0.68       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         ((k2_enumset1 @ X12 @ X13 @ X14 @ X15)
% 0.46/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ (k1_tarski @ X15)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.46/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf(t71_enumset1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.68         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.46/0.68           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.46/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X22 : $i, X23 : $i]:
% 0.46/0.68         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.46/0.68           = (k2_tarski @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['4', '7'])).
% 0.46/0.68  thf(t11_setfam_1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.46/0.68  thf('9', plain, (![X33 : $i]: ((k1_setfam_1 @ (k1_tarski @ X33)) = (X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.46/0.68  thf(t10_setfam_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.46/0.68            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]:
% 0.46/0.68         (((X31) = (k1_xboole_0))
% 0.46/0.68          | ((k1_setfam_1 @ (k2_xboole_0 @ X31 @ X32))
% 0.46/0.68              = (k3_xboole_0 @ (k1_setfam_1 @ X31) @ (k1_setfam_1 @ X32)))
% 0.46/0.68          | ((X32) = (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.68            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.46/0.68          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.68          | ((X1) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.46/0.68            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.46/0.68          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.46/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '11'])).
% 0.46/0.68  thf('13', plain, (![X33 : $i]: ((k1_setfam_1 @ (k1_tarski @ X33)) = (X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.46/0.68          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.46/0.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf(t12_setfam_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i]:
% 0.46/0.68        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.46/0.68         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.46/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.46/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.68        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.68  thf(t16_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.46/0.68          ( ( A ) = ( B ) ) ) ))).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X29 : $i, X30 : $i]:
% 0.46/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30))
% 0.46/0.68          | ((X29) != (X30)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.46/0.68      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.46/0.68        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.68  thf(t66_xboole_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.46/0.68       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.46/0.68  thf('22', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.68      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.68  thf(t3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.68            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.68          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.68          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.46/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.46/0.68          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['23', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.68  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.68          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.68          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.68          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.46/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.68          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.68          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.68  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '35'])).
% 0.46/0.68  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.46/0.68      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.68  thf('39', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.68  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '36'])).
% 0.46/0.68  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.68  thf('42', plain, ($false),
% 0.46/0.68      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.53/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
