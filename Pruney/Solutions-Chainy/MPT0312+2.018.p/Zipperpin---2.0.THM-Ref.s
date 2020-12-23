%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w8uQYOYxBw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:14 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 242 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  592 (1943 expanded)
%              Number of equality atoms :   62 ( 219 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X57 @ X59 ) @ ( k3_xboole_0 @ X58 @ X60 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k5_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ sk_C @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_D @ X0 ) ) @ sk_D ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_C ) @ sk_D ),
    inference('sup+',[status(thm)],['28','33'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('40',plain,
    ( ( k5_xboole_0 @ sk_C @ sk_D )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k5_xboole_0 @ sk_D @ sk_C )
    = ( k4_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('52',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','12','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w8uQYOYxBw
% 0.15/0.38  % Computer   : n002.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.79/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/0.99  % Solved by: fo/fo7.sh
% 0.79/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.99  % done 1303 iterations in 0.508s
% 0.79/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/0.99  % SZS output start Refutation
% 0.79/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.79/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.99  thf(t124_zfmisc_1, conjecture,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.79/0.99       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.79/0.99         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.79/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.99        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.79/0.99          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.79/0.99            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.79/0.99    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.79/0.99  thf('0', plain,
% 0.79/0.99      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.79/0.99         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(t12_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.79/0.99  thf('2', plain,
% 0.79/0.99      (![X10 : $i, X11 : $i]:
% 0.79/0.99         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.79/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.79/0.99  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['1', '2'])).
% 0.79/0.99  thf(t95_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( k3_xboole_0 @ A @ B ) =
% 0.79/0.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.79/0.99  thf('4', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X26 @ X27)
% 0.79/0.99           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.79/0.99              (k2_xboole_0 @ X26 @ X27)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.79/0.99  thf(t91_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.79/0.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.79/0.99  thf('5', plain,
% 0.79/0.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.79/0.99           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.79/0.99  thf('6', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X26 @ X27)
% 0.79/0.99           = (k5_xboole_0 @ X26 @ 
% 0.79/0.99              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.79/0.99      inference('demod', [status(thm)], ['4', '5'])).
% 0.79/0.99  thf('7', plain,
% 0.79/0.99      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.79/0.99         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['3', '6'])).
% 0.79/0.99  thf(t92_xboole_1, axiom,
% 0.79/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.79/0.99  thf('8', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.79/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.79/0.99  thf(t5_boole, axiom,
% 0.79/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.99  thf('9', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.79/0.99      inference('cnf', [status(esa)], [t5_boole])).
% 0.79/0.99  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.79/0.99  thf(t123_zfmisc_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.99     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.79/0.99       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.79/0.99  thf('11', plain,
% 0.79/0.99      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.79/0.99         ((k2_zfmisc_1 @ (k3_xboole_0 @ X57 @ X59) @ (k3_xboole_0 @ X58 @ X60))
% 0.79/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 0.79/0.99              (k2_zfmisc_1 @ X59 @ X60)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.79/0.99  thf('12', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.79/0.99              (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['10', '11'])).
% 0.79/0.99  thf('13', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X26 @ X27)
% 0.79/0.99           = (k5_xboole_0 @ X26 @ 
% 0.79/0.99              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.79/0.99      inference('demod', [status(thm)], ['4', '5'])).
% 0.79/0.99  thf('14', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.79/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.79/0.99  thf('15', plain,
% 0.79/0.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.79/0.99           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.79/0.99  thf('16', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.79/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['14', '15'])).
% 0.79/0.99  thf('17', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X26 @ X27)
% 0.79/0.99           = (k5_xboole_0 @ X26 @ 
% 0.79/0.99              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.79/0.99      inference('demod', [status(thm)], ['4', '5'])).
% 0.79/0.99  thf('18', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.79/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['14', '15'])).
% 0.79/0.99  thf('19', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.79/0.99           = (k3_xboole_0 @ X0 @ X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['17', '18'])).
% 0.79/0.99  thf(idempotence_k2_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.79/0.99  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.79/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.79/0.99  thf('21', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.79/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.79/0.99  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.79/0.99  thf('23', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('24', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['13', '23'])).
% 0.79/0.99  thf(t100_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/0.99  thf('25', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X5 @ X6)
% 0.79/0.99           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/0.99  thf('26', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k4_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.79/0.99  thf('27', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('28', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ X1 @ X0)
% 0.79/0.99           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['26', '27'])).
% 0.79/0.99  thf(t36_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.79/0.99  thf('29', plain,
% 0.79/0.99      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.79/0.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.79/0.99  thf('30', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(t110_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.79/0.99       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.79/0.99  thf('31', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X7 @ X8)
% 0.79/0.99          | ~ (r1_tarski @ X9 @ X8)
% 0.79/0.99          | (r1_tarski @ (k5_xboole_0 @ X7 @ X9) @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.79/0.99  thf('32', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((r1_tarski @ (k5_xboole_0 @ sk_C @ X0) @ sk_D)
% 0.79/0.99          | ~ (r1_tarski @ X0 @ sk_D))),
% 0.79/0.99      inference('sup-', [status(thm)], ['30', '31'])).
% 0.79/0.99  thf('33', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (r1_tarski @ (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_D @ X0)) @ sk_D)),
% 0.79/0.99      inference('sup-', [status(thm)], ['29', '32'])).
% 0.79/0.99  thf('34', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D @ sk_C) @ sk_D)),
% 0.79/0.99      inference('sup+', [status(thm)], ['28', '33'])).
% 0.79/0.99  thf(t7_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.79/0.99  thf('35', plain,
% 0.79/0.99      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.79/0.99  thf(d10_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.99  thf('36', plain,
% 0.79/0.99      (![X2 : $i, X4 : $i]:
% 0.79/0.99         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.79/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.99  thf('37', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.79/0.99          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['35', '36'])).
% 0.79/0.99  thf('38', plain, (((k2_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.79/0.99      inference('sup-', [status(thm)], ['34', '37'])).
% 0.79/0.99  thf('39', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k4_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['24', '25'])).
% 0.79/0.99  thf('40', plain,
% 0.79/0.99      (((k5_xboole_0 @ sk_C @ sk_D) = (k4_xboole_0 @ sk_D @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['38', '39'])).
% 0.79/0.99  thf('41', plain,
% 0.79/0.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.79/0.99           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.79/0.99  thf('42', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.79/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.79/0.99  thf('43', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.79/0.99           = (k1_xboole_0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['41', '42'])).
% 0.79/0.99  thf('44', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('45', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['43', '44'])).
% 0.79/0.99  thf('46', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.79/0.99      inference('cnf', [status(esa)], [t5_boole])).
% 0.79/0.99  thf('47', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.79/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.79/0.99  thf('48', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('49', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['47', '48'])).
% 0.79/0.99  thf('50', plain,
% 0.79/0.99      (((k5_xboole_0 @ sk_D @ sk_C) = (k4_xboole_0 @ sk_D @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['40', '49'])).
% 0.79/0.99  thf('51', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('52', plain,
% 0.79/0.99      (((sk_C) = (k5_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ sk_C)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['50', '51'])).
% 0.79/0.99  thf('53', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X5 @ X6)
% 0.79/0.99           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.79/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.79/0.99  thf('54', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['16', '22'])).
% 0.79/0.99  thf('55', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X1 @ X0)
% 0.79/0.99           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['53', '54'])).
% 0.79/0.99  thf('56', plain, (((sk_C) = (k3_xboole_0 @ sk_D @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['52', '55'])).
% 0.79/0.99  thf('57', plain,
% 0.79/0.99      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['0', '12', '56'])).
% 0.79/0.99  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
