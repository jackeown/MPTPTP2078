%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ITJtOD73FJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 149 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  519 (1334 expanded)
%              Number of equality atoms :   47 ( 115 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X9 ) @ ( k2_zfmisc_1 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('37',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['29'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['29'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['30','47'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['28','48'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','49','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ITJtOD73FJ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.73/2.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.73/2.93  % Solved by: fo/fo7.sh
% 2.73/2.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.93  % done 1640 iterations in 2.466s
% 2.73/2.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.73/2.93  % SZS output start Refutation
% 2.73/2.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.73/2.93  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.93  thf(sk_C_type, type, sk_C: $i).
% 2.73/2.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.73/2.93  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.93  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.93  thf(t138_zfmisc_1, conjecture,
% 2.73/2.93    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.93     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.73/2.93       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.93         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 2.73/2.93  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.93    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.93        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.73/2.93          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.93            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 2.73/2.93    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 2.73/2.93  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 2.73/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.93  thf('1', plain,
% 2.73/2.93      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 2.73/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.93  thf(t28_xboole_1, axiom,
% 2.73/2.93    (![A:$i,B:$i]:
% 2.73/2.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.73/2.93  thf('2', plain,
% 2.73/2.93      (![X4 : $i, X5 : $i]:
% 2.73/2.93         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.73/2.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.73/2.93  thf('3', plain,
% 2.73/2.93      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 2.73/2.93         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 2.73/2.93      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.93  thf(commutativity_k3_xboole_0, axiom,
% 2.73/2.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.73/2.93  thf('4', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('5', plain,
% 2.73/2.93      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 2.73/2.93         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 2.73/2.93      inference('demod', [status(thm)], ['3', '4'])).
% 2.73/2.93  thf('6', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('7', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf(t17_xboole_1, axiom,
% 2.73/2.93    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.73/2.93  thf('8', plain,
% 2.73/2.93      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 2.73/2.93      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.73/2.93  thf('9', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.73/2.93      inference('sup+', [status(thm)], ['7', '8'])).
% 2.73/2.93  thf('10', plain,
% 2.73/2.93      (![X4 : $i, X5 : $i]:
% 2.73/2.93         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.73/2.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.73/2.93  thf('11', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]:
% 2.73/2.93         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 2.73/2.93           = (k3_xboole_0 @ X1 @ X0))),
% 2.73/2.93      inference('sup-', [status(thm)], ['9', '10'])).
% 2.73/2.93  thf('12', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('13', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]:
% 2.73/2.93         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.93           = (k3_xboole_0 @ X1 @ X0))),
% 2.73/2.93      inference('demod', [status(thm)], ['11', '12'])).
% 2.73/2.93  thf('14', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]:
% 2.73/2.93         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.93           = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('sup+', [status(thm)], ['6', '13'])).
% 2.73/2.93  thf('15', plain,
% 2.73/2.93      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 2.73/2.93         (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.73/2.93         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 2.73/2.93            (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 2.73/2.93      inference('sup+', [status(thm)], ['5', '14'])).
% 2.73/2.93  thf('16', plain,
% 2.73/2.93      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 2.73/2.93         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 2.73/2.93      inference('demod', [status(thm)], ['3', '4'])).
% 2.73/2.93  thf('17', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('18', plain,
% 2.73/2.93      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 2.73/2.93         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 2.73/2.93            (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.93      inference('demod', [status(thm)], ['15', '16', '17'])).
% 2.73/2.93  thf(t123_zfmisc_1, axiom,
% 2.73/2.93    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.93     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 2.73/2.93       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 2.73/2.93  thf('19', plain,
% 2.73/2.93      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.73/2.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X15))
% 2.73/2.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 2.73/2.93              (k2_zfmisc_1 @ X14 @ X15)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.73/2.93  thf('20', plain,
% 2.73/2.93      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 2.73/2.93         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 2.73/2.93            (k3_xboole_0 @ sk_D @ sk_B)))),
% 2.73/2.93      inference('demod', [status(thm)], ['18', '19'])).
% 2.73/2.93  thf('21', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('22', plain,
% 2.73/2.93      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.73/2.93         ((k2_zfmisc_1 @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X15))
% 2.73/2.93           = (k3_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 2.73/2.93              (k2_zfmisc_1 @ X14 @ X15)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.73/2.93  thf('23', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.73/2.93      inference('sup+', [status(thm)], ['7', '8'])).
% 2.73/2.93  thf('24', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.93         (r1_tarski @ 
% 2.73/2.93          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.73/2.93          (k2_zfmisc_1 @ X2 @ X0))),
% 2.73/2.93      inference('sup+', [status(thm)], ['22', '23'])).
% 2.73/2.93  thf('25', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.93         (r1_tarski @ 
% 2.73/2.93          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.73/2.93          (k2_zfmisc_1 @ X2 @ X1))),
% 2.73/2.93      inference('sup+', [status(thm)], ['21', '24'])).
% 2.73/2.93  thf('26', plain,
% 2.73/2.93      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_D))),
% 2.73/2.93      inference('sup+', [status(thm)], ['20', '25'])).
% 2.73/2.93  thf(t117_zfmisc_1, axiom,
% 2.73/2.93    (![A:$i,B:$i,C:$i]:
% 2.73/2.93     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.73/2.93          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 2.73/2.93            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 2.73/2.93          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 2.73/2.93  thf('27', plain,
% 2.73/2.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.73/2.93         (((X9) = (k1_xboole_0))
% 2.73/2.93          | (r1_tarski @ X10 @ X11)
% 2.73/2.93          | ~ (r1_tarski @ (k2_zfmisc_1 @ X9 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.73/2.93  thf('28', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.93      inference('sup-', [status(thm)], ['26', '27'])).
% 2.73/2.93  thf('29', plain,
% 2.73/2.93      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 2.73/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.93  thf('30', plain,
% 2.73/2.93      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 2.73/2.93      inference('split', [status(esa)], ['29'])).
% 2.73/2.93  thf('31', plain,
% 2.73/2.93      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 2.73/2.93         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 2.73/2.93            (k3_xboole_0 @ sk_D @ sk_B)))),
% 2.73/2.93      inference('demod', [status(thm)], ['18', '19'])).
% 2.73/2.93  thf('32', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.93  thf('33', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.93         (r1_tarski @ 
% 2.73/2.93          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.73/2.93          (k2_zfmisc_1 @ X2 @ X0))),
% 2.73/2.93      inference('sup+', [status(thm)], ['22', '23'])).
% 2.73/2.93  thf('34', plain,
% 2.73/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.93         (r1_tarski @ 
% 2.73/2.93          (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2)) @ 
% 2.73/2.93          (k2_zfmisc_1 @ X1 @ X2))),
% 2.73/2.93      inference('sup+', [status(thm)], ['32', '33'])).
% 2.73/2.93  thf('35', plain,
% 2.73/2.93      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_B))),
% 2.73/2.93      inference('sup+', [status(thm)], ['31', '34'])).
% 2.73/2.93  thf('36', plain,
% 2.73/2.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.73/2.93         (((X9) = (k1_xboole_0))
% 2.73/2.93          | (r1_tarski @ X10 @ X11)
% 2.73/2.93          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X9) @ (k2_zfmisc_1 @ X11 @ X9)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.73/2.93  thf('37', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 2.73/2.93      inference('sup-', [status(thm)], ['35', '36'])).
% 2.73/2.93  thf('38', plain,
% 2.73/2.93      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 2.73/2.93      inference('split', [status(esa)], ['29'])).
% 2.73/2.93  thf('39', plain,
% 2.73/2.93      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 2.73/2.93      inference('sup-', [status(thm)], ['37', '38'])).
% 2.73/2.93  thf('40', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 2.73/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.93  thf('41', plain,
% 2.73/2.93      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 2.73/2.93         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 2.73/2.93      inference('sup-', [status(thm)], ['39', '40'])).
% 2.73/2.93  thf(t113_zfmisc_1, axiom,
% 2.73/2.93    (![A:$i,B:$i]:
% 2.73/2.93     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.73/2.93       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.73/2.93  thf('42', plain,
% 2.73/2.93      (![X7 : $i, X8 : $i]:
% 2.73/2.93         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.73/2.93  thf('43', plain,
% 2.73/2.93      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 2.73/2.93      inference('simplify', [status(thm)], ['42'])).
% 2.73/2.93  thf('44', plain,
% 2.73/2.93      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 2.73/2.93      inference('demod', [status(thm)], ['41', '43'])).
% 2.73/2.93  thf('45', plain, (((r1_tarski @ sk_A @ sk_C))),
% 2.73/2.93      inference('simplify', [status(thm)], ['44'])).
% 2.73/2.93  thf('46', plain,
% 2.73/2.93      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 2.73/2.93      inference('split', [status(esa)], ['29'])).
% 2.73/2.93  thf('47', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 2.73/2.93      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 2.73/2.93  thf('48', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 2.73/2.93      inference('simpl_trail', [status(thm)], ['30', '47'])).
% 2.73/2.93  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 2.73/2.93      inference('clc', [status(thm)], ['28', '48'])).
% 2.73/2.93  thf('50', plain,
% 2.73/2.93      (![X7 : $i, X8 : $i]:
% 2.73/2.93         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 2.73/2.93      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.73/2.93  thf('51', plain,
% 2.73/2.93      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 2.73/2.93      inference('simplify', [status(thm)], ['50'])).
% 2.73/2.93  thf('52', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 2.73/2.93      inference('demod', [status(thm)], ['0', '49', '51'])).
% 2.73/2.93  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 2.73/2.93  
% 2.73/2.93  % SZS output end Refutation
% 2.73/2.93  
% 2.73/2.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
