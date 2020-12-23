%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLAknCtQYH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 155 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  586 (1265 expanded)
%              Number of equality atoms :   63 ( 136 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['28','29','32','33','34','35','36','37','46'])).

thf('48',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X43 ) @ X42 )
        = X42 )
      | ~ ( r2_hidden @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLAknCtQYH
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.76/1.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.76/1.97  % Solved by: fo/fo7.sh
% 1.76/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.97  % done 2113 iterations in 1.499s
% 1.76/1.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.76/1.97  % SZS output start Refutation
% 1.76/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.76/1.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.76/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.97  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.76/1.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.76/1.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.76/1.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.76/1.97  thf(t148_zfmisc_1, conjecture,
% 1.76/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.97     ( ( ( r1_tarski @ A @ B ) & 
% 1.76/1.97         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.76/1.97         ( r2_hidden @ D @ A ) ) =>
% 1.76/1.97       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.76/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.97    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.97        ( ( ( r1_tarski @ A @ B ) & 
% 1.76/1.97            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.76/1.97            ( r2_hidden @ D @ A ) ) =>
% 1.76/1.97          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.76/1.97    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.76/1.97  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(commutativity_k3_xboole_0, axiom,
% 1.76/1.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.76/1.97  thf('1', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(t28_xboole_1, axiom,
% 1.76/1.97    (![A:$i,B:$i]:
% 1.76/1.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.76/1.97  thf('3', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i]:
% 1.76/1.97         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.76/1.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.97  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.76/1.97      inference('sup-', [status(thm)], ['2', '3'])).
% 1.76/1.97  thf('5', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('6', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['4', '5'])).
% 1.76/1.97  thf(t16_xboole_1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.76/1.97       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.76/1.97  thf('7', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf('8', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ sk_A @ X0)
% 1.76/1.97           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.76/1.97      inference('sup+', [status(thm)], ['6', '7'])).
% 1.76/1.97  thf('9', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ sk_A @ X0)
% 1.76/1.97           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.76/1.97      inference('sup+', [status(thm)], ['1', '8'])).
% 1.76/1.97  thf('10', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf(t17_xboole_1, axiom,
% 1.76/1.97    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.76/1.97  thf('11', plain,
% 1.76/1.97      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 1.76/1.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/1.97  thf('12', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.76/1.97          (k3_xboole_0 @ X2 @ X1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['10', '11'])).
% 1.76/1.97  thf('13', plain,
% 1.76/1.97      (![X0 : $i]:
% 1.76/1.97         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.76/1.97      inference('sup+', [status(thm)], ['9', '12'])).
% 1.76/1.97  thf('14', plain,
% 1.76/1.97      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C_1) @ (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['0', '13'])).
% 1.76/1.97  thf('15', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('16', plain,
% 1.76/1.97      ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('demod', [status(thm)], ['14', '15'])).
% 1.76/1.97  thf('17', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i]:
% 1.76/1.97         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.76/1.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.97  thf('18', plain,
% 1.76/1.97      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D_1))
% 1.76/1.97         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.76/1.97      inference('sup-', [status(thm)], ['16', '17'])).
% 1.76/1.97  thf('19', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf('20', plain,
% 1.76/1.97      (((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))
% 1.76/1.97         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['18', '19'])).
% 1.76/1.97  thf('21', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('22', plain,
% 1.76/1.97      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 1.76/1.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/1.97  thf('23', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i]:
% 1.76/1.97         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.76/1.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.97  thf('24', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.76/1.97           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('sup-', [status(thm)], ['22', '23'])).
% 1.76/1.97  thf('25', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('26', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.76/1.97           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('demod', [status(thm)], ['24', '25'])).
% 1.76/1.97  thf('27', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.97           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['21', '26'])).
% 1.76/1.97  thf('28', plain,
% 1.76/1.97      (((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) @ 
% 1.76/1.97         (k3_xboole_0 @ sk_C_1 @ sk_A))
% 1.76/1.97         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) @ sk_C_1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['20', '27'])).
% 1.76/1.97  thf('29', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf('30', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf('31', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('32', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.76/1.97           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/1.97      inference('sup+', [status(thm)], ['30', '31'])).
% 1.76/1.97  thf('33', plain,
% 1.76/1.97      (((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))
% 1.76/1.97         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.76/1.97      inference('demod', [status(thm)], ['18', '19'])).
% 1.76/1.97  thf('34', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.76/1.97           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['21', '26'])).
% 1.76/1.97  thf('35', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('36', plain,
% 1.76/1.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.76/1.97           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.76/1.97  thf('37', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('39', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('40', plain,
% 1.76/1.97      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 1.76/1.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/1.97  thf('41', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.76/1.97      inference('sup+', [status(thm)], ['39', '40'])).
% 1.76/1.97  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_C_1)),
% 1.76/1.97      inference('sup+', [status(thm)], ['38', '41'])).
% 1.76/1.97  thf('43', plain,
% 1.76/1.97      (![X26 : $i, X27 : $i]:
% 1.76/1.97         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.76/1.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/1.97  thf('44', plain,
% 1.76/1.97      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('sup-', [status(thm)], ['42', '43'])).
% 1.76/1.97  thf('45', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('46', plain,
% 1.76/1.97      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('demod', [status(thm)], ['44', '45'])).
% 1.76/1.97  thf('47', plain,
% 1.76/1.97      (((k3_xboole_0 @ sk_C_1 @ sk_A)
% 1.76/1.97         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.76/1.97      inference('demod', [status(thm)],
% 1.76/1.97                ['28', '29', '32', '33', '34', '35', '36', '37', '46'])).
% 1.76/1.97  thf('48', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf(l22_zfmisc_1, axiom,
% 1.76/1.97    (![A:$i,B:$i]:
% 1.76/1.97     ( ( r2_hidden @ A @ B ) =>
% 1.76/1.97       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.76/1.97  thf('49', plain,
% 1.76/1.97      (![X42 : $i, X43 : $i]:
% 1.76/1.97         (((k2_xboole_0 @ (k1_tarski @ X43) @ X42) = (X42))
% 1.76/1.97          | ~ (r2_hidden @ X43 @ X42))),
% 1.76/1.97      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 1.76/1.97  thf('50', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (sk_A))),
% 1.76/1.97      inference('sup-', [status(thm)], ['48', '49'])).
% 1.76/1.97  thf(idempotence_k3_xboole_0, axiom,
% 1.76/1.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.76/1.97  thf('51', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 1.76/1.97      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.76/1.97  thf(t23_xboole_1, axiom,
% 1.76/1.97    (![A:$i,B:$i,C:$i]:
% 1.76/1.97     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.76/1.97       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.76/1.97  thf('52', plain,
% 1.76/1.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 1.76/1.97           = (k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 1.76/1.97              (k3_xboole_0 @ X23 @ X25)))),
% 1.76/1.97      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.76/1.97  thf('53', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.76/1.97           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.76/1.97      inference('sup+', [status(thm)], ['51', '52'])).
% 1.76/1.97  thf(t22_xboole_1, axiom,
% 1.76/1.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.76/1.97  thf('54', plain,
% 1.76/1.97      (![X21 : $i, X22 : $i]:
% 1.76/1.97         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 1.76/1.97      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.76/1.97  thf('55', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]:
% 1.76/1.97         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['53', '54'])).
% 1.76/1.97  thf('56', plain,
% 1.76/1.97      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['50', '55'])).
% 1.76/1.97  thf('57', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('58', plain,
% 1.76/1.97      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('demod', [status(thm)], ['56', '57'])).
% 1.76/1.97  thf('59', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('sup+', [status(thm)], ['47', '58'])).
% 1.76/1.97  thf('60', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.97  thf('61', plain,
% 1.76/1.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.76/1.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/1.97  thf('62', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.76/1.97      inference('demod', [status(thm)], ['60', '61'])).
% 1.76/1.97  thf('63', plain, ($false),
% 1.76/1.97      inference('simplify_reflect-', [status(thm)], ['59', '62'])).
% 1.76/1.97  
% 1.76/1.97  % SZS output end Refutation
% 1.76/1.97  
% 1.81/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
