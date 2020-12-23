%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RN4gnLWD6O

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:51 EST 2020

% Result     : Theorem 15.61s
% Output     : Refutation 15.61s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 213 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  563 (1855 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ D )
          & ( r1_xboole_0 @ B @ D )
          & ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('7',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['5','6'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('9',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_D ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_C ) @ sk_D )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('24',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('41',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_A ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_D ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
    = sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('53',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ) @ sk_D ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X23 ) @ X24 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X24 ) @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('58',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ),
    inference(demod,[status(thm)],['53','56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['2','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RN4gnLWD6O
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.61/15.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.61/15.82  % Solved by: fo/fo7.sh
% 15.61/15.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.61/15.82  % done 20066 iterations in 15.375s
% 15.61/15.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.61/15.82  % SZS output start Refutation
% 15.61/15.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.61/15.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.61/15.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 15.61/15.82  thf(sk_C_type, type, sk_C: $i).
% 15.61/15.82  thf(sk_A_type, type, sk_A: $i).
% 15.61/15.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.61/15.82  thf(sk_B_type, type, sk_B: $i).
% 15.61/15.82  thf(sk_D_type, type, sk_D: $i).
% 15.61/15.82  thf(t114_xboole_1, conjecture,
% 15.61/15.82    (![A:$i,B:$i,C:$i,D:$i]:
% 15.61/15.82     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 15.61/15.82         ( r1_xboole_0 @ C @ D ) ) =>
% 15.61/15.82       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 15.61/15.82  thf(zf_stmt_0, negated_conjecture,
% 15.61/15.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 15.61/15.82        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 15.61/15.82            ( r1_xboole_0 @ C @ D ) ) =>
% 15.61/15.82          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 15.61/15.82    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 15.61/15.82  thf('0', plain,
% 15.61/15.82      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 15.61/15.82          sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf(t4_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i,C:$i]:
% 15.61/15.82     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 15.61/15.82       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.61/15.82  thf('1', plain,
% 15.61/15.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 15.61/15.82           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 15.61/15.82      inference('cnf', [status(esa)], [t4_xboole_1])).
% 15.61/15.82  thf('2', plain,
% 15.61/15.82      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 15.61/15.82          sk_D)),
% 15.61/15.82      inference('demod', [status(thm)], ['0', '1'])).
% 15.61/15.82  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf(t83_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i]:
% 15.61/15.82     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 15.61/15.82  thf('4', plain,
% 15.61/15.82      (![X20 : $i, X21 : $i]:
% 15.61/15.82         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 15.61/15.82      inference('cnf', [status(esa)], [t83_xboole_1])).
% 15.61/15.82  thf('5', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 15.61/15.82      inference('sup-', [status(thm)], ['3', '4'])).
% 15.61/15.82  thf(t82_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i]:
% 15.61/15.82     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 15.61/15.82  thf('6', plain,
% 15.61/15.82      (![X18 : $i, X19 : $i]:
% 15.61/15.82         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 15.61/15.82      inference('cnf', [status(esa)], [t82_xboole_1])).
% 15.61/15.82  thf('7', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_C) @ sk_C)),
% 15.61/15.82      inference('sup+', [status(thm)], ['5', '6'])).
% 15.61/15.82  thf(idempotence_k2_xboole_0, axiom,
% 15.61/15.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 15.61/15.82  thf('8', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 15.61/15.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 15.61/15.82  thf('9', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf(t87_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i,C:$i]:
% 15.61/15.82     ( ( r1_xboole_0 @ A @ B ) =>
% 15.61/15.82       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 15.61/15.82         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 15.61/15.82  thf('10', plain,
% 15.61/15.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ X23 @ X24)
% 15.61/15.82          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 15.61/15.82              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 15.61/15.82      inference('cnf', [status(esa)], [t87_xboole_1])).
% 15.61/15.82  thf('11', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 15.61/15.82           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_D) @ sk_C))),
% 15.61/15.82      inference('sup-', [status(thm)], ['9', '10'])).
% 15.61/15.82  thf('12', plain,
% 15.61/15.82      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_C) @ sk_D)
% 15.61/15.82         = (k4_xboole_0 @ sk_D @ sk_C))),
% 15.61/15.82      inference('sup+', [status(thm)], ['8', '11'])).
% 15.61/15.82  thf(t36_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 15.61/15.82  thf('13', plain,
% 15.61/15.82      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 15.61/15.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.61/15.82  thf(t12_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i]:
% 15.61/15.82     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 15.61/15.82  thf('14', plain,
% 15.61/15.82      (![X3 : $i, X4 : $i]:
% 15.61/15.82         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 15.61/15.82      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.61/15.82  thf('15', plain,
% 15.61/15.82      (![X0 : $i, X1 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 15.61/15.82      inference('sup-', [status(thm)], ['13', '14'])).
% 15.61/15.82  thf('16', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_C))),
% 15.61/15.82      inference('demod', [status(thm)], ['12', '15'])).
% 15.61/15.82  thf('17', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 15.61/15.82      inference('demod', [status(thm)], ['7', '16'])).
% 15.61/15.82  thf('18', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 15.61/15.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 15.61/15.82  thf('19', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf('20', plain,
% 15.61/15.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ X23 @ X24)
% 15.61/15.82          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 15.61/15.82              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 15.61/15.82      inference('cnf', [status(esa)], [t87_xboole_1])).
% 15.61/15.82  thf('21', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_D)
% 15.61/15.82           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_D) @ sk_B))),
% 15.61/15.82      inference('sup-', [status(thm)], ['19', '20'])).
% 15.61/15.82  thf('22', plain,
% 15.61/15.82      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_D)
% 15.61/15.82         = (k4_xboole_0 @ sk_D @ sk_B))),
% 15.61/15.82      inference('sup+', [status(thm)], ['18', '21'])).
% 15.61/15.82  thf('23', plain,
% 15.61/15.82      (![X0 : $i, X1 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 15.61/15.82      inference('sup-', [status(thm)], ['13', '14'])).
% 15.61/15.82  thf('24', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 15.61/15.82      inference('demod', [status(thm)], ['22', '23'])).
% 15.61/15.82  thf('25', plain,
% 15.61/15.82      (![X18 : $i, X19 : $i]:
% 15.61/15.82         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 15.61/15.82      inference('cnf', [status(esa)], [t82_xboole_1])).
% 15.61/15.82  thf(t70_xboole_1, axiom,
% 15.61/15.82    (![A:$i,B:$i,C:$i]:
% 15.61/15.82     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 15.61/15.82            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 15.61/15.82       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 15.61/15.82            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 15.61/15.82  thf('26', plain,
% 15.61/15.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 15.61/15.82         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 15.61/15.82          | ~ (r1_xboole_0 @ X14 @ X15)
% 15.61/15.82          | ~ (r1_xboole_0 @ X14 @ X16))),
% 15.61/15.82      inference('cnf', [status(esa)], [t70_xboole_1])).
% 15.61/15.82  thf('27', plain,
% 15.61/15.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 15.61/15.82          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 15.61/15.82             (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 15.61/15.82      inference('sup-', [status(thm)], ['25', '26'])).
% 15.61/15.82  thf('28', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ sk_D @ X0)
% 15.61/15.82          | (r1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ 
% 15.61/15.82             (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D) @ X0)))),
% 15.61/15.82      inference('sup-', [status(thm)], ['24', '27'])).
% 15.61/15.82  thf('29', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 15.61/15.82      inference('demod', [status(thm)], ['22', '23'])).
% 15.61/15.82  thf('30', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf('31', plain,
% 15.61/15.82      (![X20 : $i, X21 : $i]:
% 15.61/15.82         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 15.61/15.82      inference('cnf', [status(esa)], [t83_xboole_1])).
% 15.61/15.82  thf('32', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 15.61/15.82      inference('sup-', [status(thm)], ['30', '31'])).
% 15.61/15.82  thf('33', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ sk_D @ X0)
% 15.61/15.82          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0)))),
% 15.61/15.82      inference('demod', [status(thm)], ['28', '29', '32'])).
% 15.61/15.82  thf('34', plain, ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_C))),
% 15.61/15.82      inference('sup-', [status(thm)], ['17', '33'])).
% 15.61/15.82  thf('35', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 15.61/15.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 15.61/15.82  thf('36', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf('37', plain,
% 15.61/15.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ X23 @ X24)
% 15.61/15.82          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 15.61/15.82              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 15.61/15.82      inference('cnf', [status(esa)], [t87_xboole_1])).
% 15.61/15.82  thf('38', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_D)
% 15.61/15.82           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_D) @ sk_A))),
% 15.61/15.82      inference('sup-', [status(thm)], ['36', '37'])).
% 15.61/15.82  thf('39', plain,
% 15.61/15.82      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_A) @ sk_D)
% 15.61/15.82         = (k4_xboole_0 @ sk_D @ sk_A))),
% 15.61/15.82      inference('sup+', [status(thm)], ['35', '38'])).
% 15.61/15.82  thf('40', plain,
% 15.61/15.82      (![X0 : $i, X1 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 15.61/15.82      inference('sup-', [status(thm)], ['13', '14'])).
% 15.61/15.82  thf('41', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_A))),
% 15.61/15.82      inference('demod', [status(thm)], ['39', '40'])).
% 15.61/15.82  thf('42', plain,
% 15.61/15.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 15.61/15.82          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 15.61/15.82             (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 15.61/15.82      inference('sup-', [status(thm)], ['25', '26'])).
% 15.61/15.82  thf('43', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ sk_D @ X0)
% 15.61/15.82          | (r1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_A) @ 
% 15.61/15.82             (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_D) @ X0)))),
% 15.61/15.82      inference('sup-', [status(thm)], ['41', '42'])).
% 15.61/15.82  thf('44', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_A))),
% 15.61/15.82      inference('demod', [status(thm)], ['39', '40'])).
% 15.61/15.82  thf('45', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 15.61/15.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.61/15.82  thf('46', plain,
% 15.61/15.82      (![X20 : $i, X21 : $i]:
% 15.61/15.82         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 15.61/15.82      inference('cnf', [status(esa)], [t83_xboole_1])).
% 15.61/15.82  thf('47', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 15.61/15.82      inference('sup-', [status(thm)], ['45', '46'])).
% 15.61/15.82  thf('48', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ sk_D @ X0)
% 15.61/15.82          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 15.61/15.82      inference('demod', [status(thm)], ['43', '44', '47'])).
% 15.61/15.82  thf('49', plain,
% 15.61/15.82      ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 15.61/15.82      inference('sup-', [status(thm)], ['34', '48'])).
% 15.61/15.82  thf('50', plain,
% 15.61/15.82      (![X20 : $i, X21 : $i]:
% 15.61/15.82         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 15.61/15.82      inference('cnf', [status(esa)], [t83_xboole_1])).
% 15.61/15.82  thf('51', plain,
% 15.61/15.82      (((k4_xboole_0 @ sk_D @ 
% 15.61/15.82         (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) = (sk_D))),
% 15.61/15.82      inference('sup-', [status(thm)], ['49', '50'])).
% 15.61/15.82  thf('52', plain,
% 15.61/15.82      (![X18 : $i, X19 : $i]:
% 15.61/15.82         (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X19 @ X18))),
% 15.61/15.82      inference('cnf', [status(esa)], [t82_xboole_1])).
% 15.61/15.82  thf('53', plain,
% 15.61/15.82      ((r1_xboole_0 @ 
% 15.61/15.82        (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 15.61/15.82         sk_D) @ 
% 15.61/15.82        sk_D)),
% 15.61/15.82      inference('sup+', [status(thm)], ['51', '52'])).
% 15.61/15.82  thf('54', plain, ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_C))),
% 15.61/15.82      inference('sup-', [status(thm)], ['17', '33'])).
% 15.61/15.82  thf('55', plain,
% 15.61/15.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.61/15.82         (~ (r1_xboole_0 @ X23 @ X24)
% 15.61/15.82          | ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X23) @ X24)
% 15.61/15.82              = (k4_xboole_0 @ (k2_xboole_0 @ X25 @ X24) @ X23)))),
% 15.61/15.82      inference('cnf', [status(esa)], [t87_xboole_1])).
% 15.61/15.82  thf('56', plain,
% 15.61/15.82      (![X0 : $i]:
% 15.61/15.82         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D) @ 
% 15.61/15.82           (k2_xboole_0 @ sk_B @ sk_C))
% 15.61/15.82           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 15.61/15.82              sk_D))),
% 15.61/15.82      inference('sup-', [status(thm)], ['54', '55'])).
% 15.61/15.82  thf('57', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 15.61/15.82      inference('sup-', [status(thm)], ['45', '46'])).
% 15.61/15.82  thf('58', plain,
% 15.61/15.82      ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ sk_D)),
% 15.61/15.82      inference('demod', [status(thm)], ['53', '56', '57'])).
% 15.61/15.82  thf('59', plain, ($false), inference('demod', [status(thm)], ['2', '58'])).
% 15.61/15.82  
% 15.61/15.82  % SZS output end Refutation
% 15.61/15.82  
% 15.61/15.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
