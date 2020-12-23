%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.If9DxoPk3z

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 569 expanded)
%              Number of leaves         :   29 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          :  624 (4445 expanded)
%              Number of equality atoms :   70 ( 598 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X51 ) @ X52 )
      | ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','14'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X55 @ X57 ) @ X58 )
      | ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( r2_hidden @ X55 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['5','21'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','22'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['29','41'])).

thf('43',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['5','21'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['5','21'])).

thf('46',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X51 ) @ X52 )
      | ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X55 @ X57 ) @ X58 )
      | ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( r2_hidden @ X55 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( k3_tarski @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_B ) ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['44','51'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B = sk_C )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['43','64'])).

thf('66',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','69'])).

thf('71',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.18  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.If9DxoPk3z
% 0.18/0.38  % Computer   : n024.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 14:15:06 EST 2020
% 0.18/0.38  % CPUTime    : 
% 0.18/0.38  % Running portfolio for 600 s
% 0.18/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.39  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 141 iterations in 0.042s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(t44_zfmisc_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.50          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.24/0.50          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.50        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.24/0.50             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.24/0.50             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.24/0.50  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t7_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.24/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.50  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.24/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf(d10_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X7 : $i, X9 : $i]:
% 0.24/0.50         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.24/0.50        | ((k1_tarski @ sk_A) = (sk_B)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('7', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.24/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.50  thf(l27_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X51 : $i, X52 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ (k1_tarski @ X51) @ X52) | (r2_hidden @ X51 @ X52))),
% 0.24/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.24/0.50  thf('9', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.24/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf(t67_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.24/0.50         ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.50         (((X12) = (k1_xboole_0))
% 0.24/0.50          | ~ (r1_tarski @ X12 @ X13)
% 0.24/0.50          | ~ (r1_tarski @ X12 @ X14)
% 0.24/0.50          | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.24/0.50      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.24/0.50          | ~ (r1_tarski @ sk_B @ X0)
% 0.24/0.50          | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.50  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['8', '13'])).
% 0.24/0.50  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['7', '14'])).
% 0.24/0.50  thf('16', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['7', '14'])).
% 0.24/0.50  thf(t38_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X55 : $i, X57 : $i, X58 : $i]:
% 0.24/0.50         ((r1_tarski @ (k2_tarski @ X55 @ X57) @ X58)
% 0.24/0.50          | ~ (r2_hidden @ X57 @ X58)
% 0.24/0.50          | ~ (r2_hidden @ X55 @ X58))),
% 0.24/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.24/0.50          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['15', '18'])).
% 0.24/0.50  thf(t69_enumset1, axiom,
% 0.24/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.50  thf('20', plain,
% 0.24/0.50      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.24/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.50  thf('22', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['5', '21'])).
% 0.24/0.50  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '22'])).
% 0.24/0.50  thf(t95_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( k3_xboole_0 @ A @ B ) =
% 0.24/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.24/0.50  thf('24', plain,
% 0.24/0.50      (![X21 : $i, X22 : $i]:
% 0.24/0.50         ((k3_xboole_0 @ X21 @ X22)
% 0.24/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.24/0.50              (k2_xboole_0 @ X21 @ X22)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.24/0.50  thf(t91_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.24/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.24/0.50           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.24/0.50  thf('26', plain,
% 0.24/0.50      (![X21 : $i, X22 : $i]:
% 0.24/0.50         ((k3_xboole_0 @ X21 @ X22)
% 0.24/0.50           = (k5_xboole_0 @ X21 @ 
% 0.24/0.50              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.24/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.24/0.50  thf('27', plain,
% 0.24/0.50      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.24/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.24/0.50      inference('sup+', [status(thm)], ['23', '26'])).
% 0.24/0.50  thf(commutativity_k5_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.24/0.50  thf('28', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.24/0.50  thf('29', plain,
% 0.24/0.50      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.24/0.50         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.24/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.24/0.50  thf(t92_xboole_1, axiom,
% 0.24/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.50  thf('30', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.24/0.50  thf('31', plain,
% 0.24/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.24/0.50           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.24/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.24/0.50  thf('32', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.24/0.50           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.24/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.24/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.24/0.50  thf('33', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.24/0.50  thf('34', plain,
% 0.24/0.50      (![X21 : $i, X22 : $i]:
% 0.24/0.50         ((k3_xboole_0 @ X21 @ X22)
% 0.24/0.50           = (k5_xboole_0 @ X21 @ 
% 0.24/0.50              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.24/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.24/0.50  thf('35', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((k3_xboole_0 @ X0 @ X0)
% 0.24/0.50           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.24/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.24/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.24/0.50  thf('36', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.24/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.24/0.50  thf('37', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.24/0.50  thf('38', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.24/0.50  thf('39', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.24/0.50  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.50  thf('41', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.24/0.50      inference('demod', [status(thm)], ['32', '40'])).
% 0.24/0.50  thf('42', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['29', '41'])).
% 0.24/0.50  thf('43', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '22'])).
% 0.24/0.50  thf('44', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['5', '21'])).
% 0.24/0.50  thf('45', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['5', '21'])).
% 0.24/0.50  thf('46', plain,
% 0.24/0.50      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf(l51_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.50  thf('47', plain,
% 0.24/0.50      (![X53 : $i, X54 : $i]:
% 0.24/0.50         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.24/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.24/0.50  thf('48', plain,
% 0.24/0.50      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['46', '47'])).
% 0.24/0.50  thf('49', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.24/0.50  thf('50', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['48', '49'])).
% 0.24/0.50  thf('51', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 0.24/0.50      inference('sup+', [status(thm)], ['45', '50'])).
% 0.24/0.50  thf('52', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['44', '51'])).
% 0.24/0.50  thf('53', plain,
% 0.24/0.50      (![X51 : $i, X52 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ (k1_tarski @ X51) @ X52) | (r2_hidden @ X51 @ X52))),
% 0.24/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.24/0.50  thf('54', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['52', '53'])).
% 0.24/0.50  thf('55', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['52', '53'])).
% 0.24/0.50  thf('56', plain,
% 0.24/0.50      (![X55 : $i, X57 : $i, X58 : $i]:
% 0.24/0.50         ((r1_tarski @ (k2_tarski @ X55 @ X57) @ X58)
% 0.24/0.50          | ~ (r2_hidden @ X57 @ X58)
% 0.24/0.50          | ~ (r2_hidden @ X55 @ X58))),
% 0.24/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.50  thf('57', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0)
% 0.24/0.50          | ~ (r2_hidden @ X1 @ X0)
% 0.24/0.50          | (r1_tarski @ (k2_tarski @ X1 @ (k3_tarski @ sk_B)) @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.24/0.50  thf('58', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0)
% 0.24/0.50          | (r1_tarski @ 
% 0.24/0.50             (k2_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_B)) @ X0)
% 0.24/0.50          | (r1_xboole_0 @ sk_B @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['54', '57'])).
% 0.24/0.50  thf('59', plain,
% 0.24/0.50      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.24/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.50  thf('60', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 0.24/0.50      inference('demod', [status(thm)], ['44', '51'])).
% 0.24/0.50  thf('61', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0)
% 0.24/0.50          | (r1_tarski @ sk_B @ X0)
% 0.24/0.50          | (r1_xboole_0 @ sk_B @ X0))),
% 0.24/0.50      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.24/0.50  thf('62', plain,
% 0.24/0.50      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.24/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.24/0.50  thf(t12_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.24/0.50  thf('63', plain,
% 0.24/0.50      (![X10 : $i, X11 : $i]:
% 0.24/0.50         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.24/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.24/0.50  thf('64', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r1_xboole_0 @ sk_B @ X0) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.24/0.50  thf('65', plain, ((((sk_B) = (sk_C)) | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.50      inference('sup+', [status(thm)], ['43', '64'])).
% 0.24/0.50  thf('66', plain, (((sk_B) != (sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('67', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.24/0.50  thf(d7_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('68', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.50  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.24/0.50  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['42', '69'])).
% 0.24/0.50  thf('71', plain, (((sk_C) != (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('72', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
