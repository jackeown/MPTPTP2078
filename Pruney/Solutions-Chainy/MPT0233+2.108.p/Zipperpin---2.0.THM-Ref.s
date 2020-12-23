%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Epf33W8kK1

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:48 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 118 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  624 ( 849 expanded)
%              Number of equality atoms :   74 ( 107 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( r1_tarski @ X59 @ ( k2_tarski @ X57 @ X60 ) )
      | ( X59
       != ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X57: $i,X60: $i] :
      ( r1_tarski @ ( k1_tarski @ X57 ) @ ( k2_tarski @ X57 @ X60 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','31'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('33',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X53 @ X55 ) @ X56 )
        = ( k1_tarski @ X53 ) )
      | ( X53 != X55 )
      | ( r2_hidden @ X53 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('34',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X55 @ X55 ) @ X56 )
        = ( k1_tarski @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X55 ) @ X56 )
        = ( k1_tarski @ X55 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('39',plain,(
    ! [X61: $i,X62: $i] :
      ( ( X62 != X61 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X62 ) @ ( k1_tarski @ X61 ) )
       != ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('40',plain,(
    ! [X61: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X61 ) )
     != ( k1_tarski @ X61 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X61: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X61 ) )
     != ( k1_tarski @ X61 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( r1_tarski @ X59 @ ( k2_tarski @ X57 @ X60 ) )
      | ( X59 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('47',plain,(
    ! [X57: $i,X60: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X57 @ X60 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','51'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X21 )
      | ( X23 = X22 )
      | ( X23 = X19 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('54',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X23 = X19 )
      | ( X23 = X22 )
      | ~ ( r2_hidden @ X23 @ ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Epf33W8kK1
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 461 iterations in 0.163s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.64  thf(t70_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf(l45_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.46/0.64       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.46/0.64            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X57 : $i, X59 : $i, X60 : $i]:
% 0.46/0.64         ((r1_tarski @ X59 @ (k2_tarski @ X57 @ X60))
% 0.46/0.64          | ((X59) != (k1_tarski @ X57)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X57 : $i, X60 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_tarski @ X57) @ (k2_tarski @ X57 @ X60))),
% 0.46/0.64      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '2'])).
% 0.46/0.64  thf(t28_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.64          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.64             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t28_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.46/0.64         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (((k3_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.46/0.64         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t18_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         ((r1_tarski @ X10 @ X11)
% 0.46/0.64          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1))
% 0.46/0.64          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.46/0.64         = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.46/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf(t3_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('20', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.64           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.64  thf('23', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '25'])).
% 0.46/0.64  thf(t4_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.46/0.64          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.46/0.64          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.64  thf('29', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.46/0.64         = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '31'])).
% 0.46/0.64  thf(l38_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.46/0.64         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ (k2_tarski @ X53 @ X55) @ X56) = (k1_tarski @ X53))
% 0.46/0.64          | ((X53) != (X55))
% 0.46/0.64          | (r2_hidden @ X53 @ X56))),
% 0.46/0.64      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X55 : $i, X56 : $i]:
% 0.46/0.64         ((r2_hidden @ X55 @ X56)
% 0.46/0.64          | ((k4_xboole_0 @ (k2_tarski @ X55 @ X55) @ X56) = (k1_tarski @ X55)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X55 : $i, X56 : $i]:
% 0.46/0.64         ((r2_hidden @ X55 @ X56)
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X55) @ X56) = (k1_tarski @ X55)))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.46/0.64        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '25'])).
% 0.46/0.64  thf(t20_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.64         ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ( A ) != ( B ) ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X61 : $i, X62 : $i]:
% 0.46/0.64         (((X62) != (X61))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X62) @ (k1_tarski @ X61))
% 0.46/0.64              != (k1_tarski @ X62)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X61 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X61))
% 0.46/0.64           != (k1_tarski @ X61))),
% 0.46/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X61 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X61))
% 0.46/0.64           != (k1_tarski @ X61))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X57 : $i, X59 : $i, X60 : $i]:
% 0.46/0.64         ((r1_tarski @ X59 @ (k2_tarski @ X57 @ X60))
% 0.46/0.64          | ((X59) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X57 : $i, X60 : $i]:
% 0.46/0.64         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X57 @ X60))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['45', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '44', '50'])).
% 0.46/0.64  thf('52', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.46/0.64      inference('clc', [status(thm)], ['37', '51'])).
% 0.46/0.64  thf(d2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X23 @ X21)
% 0.46/0.64          | ((X23) = (X22))
% 0.46/0.64          | ((X23) = (X19))
% 0.46/0.64          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X19 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (((X23) = (X19))
% 0.46/0.64          | ((X23) = (X22))
% 0.46/0.64          | ~ (r2_hidden @ X23 @ (k2_tarski @ X22 @ X19)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.46/0.64  thf('55', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['52', '54'])).
% 0.46/0.64  thf('56', plain, (((sk_A) != (sk_D_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('57', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('58', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['55', '56', '57'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.51/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
