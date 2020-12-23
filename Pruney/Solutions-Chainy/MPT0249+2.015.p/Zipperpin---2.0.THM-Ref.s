%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tN5Y4kIH5F

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 257 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  546 (2019 expanded)
%              Number of equality atoms :   65 ( 254 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X57 @ X59 ) @ X60 )
      | ~ ( r2_hidden @ X59 @ X60 )
      | ~ ( r2_hidden @ X57 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B )
    | ( ( k3_xboole_0 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','24'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = sk_C )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','42'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','54'])).

thf('56',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tN5Y4kIH5F
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:12 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 140 iterations in 0.061s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(t44_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.52          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.52        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.52             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.52  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(l27_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X53 : $i, X54 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 0.22/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.52  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t7_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.52  thf('4', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t63_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.52       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X12 @ X13)
% 0.22/0.52          | ~ (r1_xboole_0 @ X13 @ X14)
% 0.22/0.52          | (r1_xboole_0 @ X12 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.52  thf(t38_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X57 : $i, X59 : $i, X60 : $i]:
% 0.22/0.52         ((r1_tarski @ (k2_tarski @ X57 @ X59) @ X60)
% 0.22/0.52          | ~ (r2_hidden @ X59 @ X60)
% 0.22/0.52          | ~ (r2_hidden @ X57 @ X60))),
% 0.22/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k2_tarski @ X1 @ sk_A) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.52          | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ X0)
% 0.22/0.52          | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.22/0.52          | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.52  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X7 : $i, X9 : $i]:
% 0.22/0.52         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.22/0.52        | ((k1_tarski @ sk_A) = (sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_B @ sk_B) | ((k1_tarski @ sk_A) = (sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.52  thf(d7_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (sk_B))
% 0.22/0.52        | ((k3_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.52  thf('21', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((((k1_tarski @ sk_A) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('24', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '24'])).
% 0.22/0.52  thf(t95_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X23 @ X24)
% 0.22/0.52           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.22/0.52              (k2_xboole_0 @ X23 @ X24)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.52  thf(t91_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.22/0.52           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X23 @ X24)
% 0.22/0.52           = (k5_xboole_0 @ X23 @ 
% 0.22/0.52              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.22/0.52         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['25', '28'])).
% 0.22/0.52  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.22/0.52         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '24'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.52  thf('34', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf(t12_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_B @ X0) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_xboole_0 @ sk_B @ X0) = (X0))
% 0.22/0.52          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((((sk_B) = (sk_C)) | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['32', '39'])).
% 0.22/0.52  thf('41', plain, (((sk_B) != (sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (((k1_xboole_0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '42'])).
% 0.22/0.52  thf(t92_xboole_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('44', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.22/0.52           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.52  thf('47', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X23 @ X24)
% 0.22/0.52           = (k5_xboole_0 @ X23 @ 
% 0.22/0.52              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X0 @ X0)
% 0.22/0.52           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.52  thf('51', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.52  thf('52', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['46', '54'])).
% 0.22/0.52  thf('56', plain, (((k1_xboole_0) = (sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['43', '55'])).
% 0.22/0.52  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('58', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
