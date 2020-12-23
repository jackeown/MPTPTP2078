%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhpupSq217

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:02 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 171 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  402 ( 998 expanded)
%              Number of equality atoms :   34 (  84 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('32',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','13'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k2_tarski @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','35'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhpupSq217
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 260 iterations in 0.179s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(t7_xboole_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf(t50_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.66        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_2) @ sk_C_1) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf(t7_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('7', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf(t28_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('9', plain, (((k3_xboole_0 @ sk_C_1 @ k1_xboole_0) = (sk_C_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf(t4_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.66            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.66          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ sk_C_1) | ~ (r1_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.66  thf('12', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.66  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.46/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_2))
% 0.46/0.66         = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf(d1_xboole_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('20', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.46/0.66          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.66          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.66  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.46/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('32', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '13'])).
% 0.46/0.66  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B_2))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '34'])).
% 0.46/0.66  thf('36', plain, (((k2_tarski @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '35'])).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X27 : $i, X28 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(d1_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_2, axiom,
% 0.46/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.46/0.66          | (r2_hidden @ X20 @ X24)
% 0.46/0.66          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.46/0.66          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['37', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.66         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.46/0.66         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.46/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['36', '45'])).
% 0.46/0.66  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.66  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
