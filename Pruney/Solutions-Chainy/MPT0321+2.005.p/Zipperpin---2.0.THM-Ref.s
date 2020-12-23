%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJiIbJJr0z

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:33 EST 2020

% Result     : Theorem 9.71s
% Output     : Refutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :  193 (2124 expanded)
%              Number of leaves         :   20 ( 691 expanded)
%              Depth                    :   30
%              Number of atoms          : 1667 (22523 expanded)
%              Number of equality atoms :  171 (2797 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_D )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','26','27','28'])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['54','55'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['54','55'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_xboole_0 @ sk_C @ X0 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ sk_A )
      | ( ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('89',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C = sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('94',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('114',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('120',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('121',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('126',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['54','55'])).

thf('128',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('130',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('132',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('134',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('136',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['134','135'])).

thf('138',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_D )
      = ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['118','119','136','137','140'])).

thf('142',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) ),
    inference('sup+',[status(thm)],['111','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('144',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['54','55'])).

thf('145',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('153',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['106','153'])).

thf('155',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['90'])).

thf('156',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B != sk_D ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    sk_B = sk_D ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['90'])).

thf('159',plain,(
    sk_A != sk_C ),
    inference('sat_resolution*',[status(thm)],['157','158'])).

thf('160',plain,(
    sk_A != sk_C ),
    inference(simpl_trail,[status(thm)],['91','159'])).

thf('161',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['89','160'])).

thf('162',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('163',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('168',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['106','153'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['162','169'])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['161','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJiIbJJr0z
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:14:56 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.71/9.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.71/9.89  % Solved by: fo/fo7.sh
% 9.71/9.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.71/9.89  % done 7889 iterations in 9.426s
% 9.71/9.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.71/9.89  % SZS output start Refutation
% 9.71/9.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.71/9.89  thf(sk_B_type, type, sk_B: $i).
% 9.71/9.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.71/9.89  thf(sk_C_type, type, sk_C: $i).
% 9.71/9.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.71/9.89  thf(sk_A_type, type, sk_A: $i).
% 9.71/9.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.71/9.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.71/9.89  thf(sk_D_type, type, sk_D: $i).
% 9.71/9.89  thf(t134_zfmisc_1, conjecture,
% 9.71/9.89    (![A:$i,B:$i,C:$i,D:$i]:
% 9.71/9.89     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 9.71/9.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.71/9.89         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 9.71/9.89  thf(zf_stmt_0, negated_conjecture,
% 9.71/9.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 9.71/9.89        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 9.71/9.89          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.71/9.89            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 9.71/9.89    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 9.71/9.89  thf('0', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf(t123_zfmisc_1, axiom,
% 9.71/9.89    (![A:$i,B:$i,C:$i,D:$i]:
% 9.71/9.89     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 9.71/9.89       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 9.71/9.89  thf('1', plain,
% 9.71/9.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X24 @ X25)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 9.71/9.89  thf('2', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X1 @ X0)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['0', '1'])).
% 9.71/9.89  thf('3', plain,
% 9.71/9.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X24 @ X25)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 9.71/9.89  thf('4', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 9.71/9.89           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 9.71/9.89              (k3_xboole_0 @ sk_D @ X0)))),
% 9.71/9.89      inference('demod', [status(thm)], ['2', '3'])).
% 9.71/9.89  thf('5', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf(t120_zfmisc_1, axiom,
% 9.71/9.89    (![A:$i,B:$i,C:$i]:
% 9.71/9.89     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 9.71/9.89         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 9.71/9.89       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 9.71/9.89         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 9.71/9.89  thf('6', plain,
% 9.71/9.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('7', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['5', '6'])).
% 9.71/9.89  thf('8', plain,
% 9.71/9.89      (![X18 : $i, X20 : $i, X21 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X21 @ X20)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('9', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 9.71/9.89      inference('sup+', [status(thm)], ['7', '8'])).
% 9.71/9.89  thf(commutativity_k2_xboole_0, axiom,
% 9.71/9.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.71/9.89  thf('10', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('11', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 9.71/9.89      inference('demod', [status(thm)], ['9', '10'])).
% 9.71/9.89  thf('12', plain,
% 9.71/9.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X24 @ X25)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 9.71/9.89  thf('13', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C @ sk_A)) @ 
% 9.71/9.89           (k3_xboole_0 @ X0 @ sk_B))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 9.71/9.89              (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B))))),
% 9.71/9.89      inference('sup+', [status(thm)], ['11', '12'])).
% 9.71/9.89  thf('14', plain,
% 9.71/9.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X24 @ X25)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 9.71/9.89  thf('15', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C @ sk_A)) @ 
% 9.71/9.89           (k3_xboole_0 @ X0 @ sk_B))
% 9.71/9.89           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C) @ 
% 9.71/9.89              (k3_xboole_0 @ X0 @ (k2_xboole_0 @ sk_D @ sk_B))))),
% 9.71/9.89      inference('demod', [status(thm)], ['13', '14'])).
% 9.71/9.89  thf('16', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_A)) @ 
% 9.71/9.89         (k3_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 9.71/9.89            (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ sk_B))))),
% 9.71/9.89      inference('sup+', [status(thm)], ['4', '15'])).
% 9.71/9.89  thf(t21_xboole_1, axiom,
% 9.71/9.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 9.71/9.89  thf('17', plain,
% 9.71/9.89      (![X8 : $i, X9 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 9.71/9.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.71/9.89  thf('18', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('19', plain,
% 9.71/9.89      (![X8 : $i, X9 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 9.71/9.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.71/9.89  thf('20', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['18', '19'])).
% 9.71/9.89  thf('21', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['5', '6'])).
% 9.71/9.89  thf('22', plain,
% 9.71/9.89      (![X8 : $i, X9 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 9.71/9.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.71/9.89  thf('23', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))
% 9.71/9.89           = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['21', '22'])).
% 9.71/9.89  thf('24', plain,
% 9.71/9.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 9.71/9.89           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X24 @ X25)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 9.71/9.89  thf('25', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 9.71/9.89           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['23', '24'])).
% 9.71/9.89  thf('26', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['20', '25'])).
% 9.71/9.89  thf(commutativity_k3_xboole_0, axiom,
% 9.71/9.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.71/9.89  thf('27', plain,
% 9.71/9.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.71/9.89  thf('28', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['18', '19'])).
% 9.71/9.89  thf('29', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_C @ sk_D)
% 9.71/9.89         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 9.71/9.89      inference('demod', [status(thm)], ['16', '17', '26', '27', '28'])).
% 9.71/9.89  thf('30', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf(t117_zfmisc_1, axiom,
% 9.71/9.89    (![A:$i,B:$i,C:$i]:
% 9.71/9.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 9.71/9.89          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 9.71/9.89            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 9.71/9.89          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 9.71/9.89  thf('31', plain,
% 9.71/9.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.71/9.89         (((X15) = (k1_xboole_0))
% 9.71/9.89          | (r1_tarski @ X16 @ X17)
% 9.71/9.89          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 9.71/9.89               (k2_zfmisc_1 @ X17 @ X15)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 9.71/9.89  thf('32', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89             (k2_zfmisc_1 @ X0 @ sk_B))
% 9.71/9.89          | (r1_tarski @ sk_A @ X0)
% 9.71/9.89          | ((sk_B) = (k1_xboole_0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['30', '31'])).
% 9.71/9.89  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('34', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89             (k2_zfmisc_1 @ X0 @ sk_B))
% 9.71/9.89          | (r1_tarski @ sk_A @ X0))),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 9.71/9.89  thf('35', plain,
% 9.71/9.89      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89           (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['29', '34'])).
% 9.71/9.89  thf(d10_xboole_0, axiom,
% 9.71/9.89    (![A:$i,B:$i]:
% 9.71/9.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.71/9.89  thf('36', plain,
% 9.71/9.89      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 9.71/9.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.71/9.89  thf('37', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.71/9.89      inference('simplify', [status(thm)], ['36'])).
% 9.71/9.89  thf('38', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))),
% 9.71/9.89      inference('demod', [status(thm)], ['35', '37'])).
% 9.71/9.89  thf('39', plain,
% 9.71/9.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.71/9.89  thf(idempotence_k3_xboole_0, axiom,
% 9.71/9.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 9.71/9.89  thf('40', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 9.71/9.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 9.71/9.89  thf(t23_xboole_1, axiom,
% 9.71/9.89    (![A:$i,B:$i,C:$i]:
% 9.71/9.89     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 9.71/9.89       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 9.71/9.89  thf('41', plain,
% 9.71/9.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 9.71/9.89           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 9.71/9.89              (k3_xboole_0 @ X10 @ X12)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t23_xboole_1])).
% 9.71/9.89  thf('42', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 9.71/9.89           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['40', '41'])).
% 9.71/9.89  thf('43', plain,
% 9.71/9.89      (![X8 : $i, X9 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 9.71/9.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.71/9.89  thf('44', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('45', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['39', '44'])).
% 9.71/9.89  thf('46', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf(t7_xboole_1, axiom,
% 9.71/9.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.71/9.89  thf('47', plain,
% 9.71/9.89      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 9.71/9.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.71/9.89  thf('48', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['46', '47'])).
% 9.71/9.89  thf('49', plain,
% 9.71/9.89      (![X5 : $i, X7 : $i]:
% 9.71/9.89         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 9.71/9.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.71/9.89  thf('50', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.71/9.89          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['48', '49'])).
% 9.71/9.89  thf('51', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.71/9.89          | ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.71/9.89              = (k3_xboole_0 @ X1 @ X0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['45', '50'])).
% 9.71/9.89  thf('52', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['39', '44'])).
% 9.71/9.89  thf('53', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.71/9.89          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 9.71/9.89      inference('demod', [status(thm)], ['51', '52'])).
% 9.71/9.89  thf('54', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 9.71/9.89      inference('sup-', [status(thm)], ['38', '53'])).
% 9.71/9.89  thf('55', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('56', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['54', '55'])).
% 9.71/9.89  thf('57', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('58', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['18', '19'])).
% 9.71/9.89  thf('59', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 9.71/9.89           = (k3_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['57', '58'])).
% 9.71/9.89  thf('60', plain,
% 9.71/9.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.71/9.89  thf('61', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 9.71/9.89           = (k3_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('demod', [status(thm)], ['59', '60'])).
% 9.71/9.89  thf('62', plain,
% 9.71/9.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.71/9.89  thf('63', plain,
% 9.71/9.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 9.71/9.89           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 9.71/9.89              (k3_xboole_0 @ X10 @ X12)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t23_xboole_1])).
% 9.71/9.89  thf('64', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 9.71/9.89           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['62', '63'])).
% 9.71/9.89  thf('65', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X1))
% 9.71/9.89           = (k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 9.71/9.89              (k3_xboole_0 @ X1 @ X0)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['61', '64'])).
% 9.71/9.89  thf('66', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('67', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('68', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X1))
% 9.71/9.89           = (k3_xboole_0 @ X1 @ X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['65', '66', '67'])).
% 9.71/9.89  thf('69', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)
% 9.71/9.89           = (k3_xboole_0 @ sk_A @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['56', '68'])).
% 9.71/9.89  thf('70', plain,
% 9.71/9.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.71/9.89  thf('71', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 9.71/9.89           = (k3_xboole_0 @ sk_A @ X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['69', '70'])).
% 9.71/9.89  thf('72', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('73', plain,
% 9.71/9.89      (![X0 : $i]: ((k2_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['71', '72'])).
% 9.71/9.89  thf('74', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['54', '55'])).
% 9.71/9.89  thf('75', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['18', '19'])).
% 9.71/9.89  thf('76', plain,
% 9.71/9.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 9.71/9.89           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 9.71/9.89              (k3_xboole_0 @ X10 @ X12)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t23_xboole_1])).
% 9.71/9.89  thf('77', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 9.71/9.89           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['75', '76'])).
% 9.71/9.89  thf('78', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('79', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 9.71/9.89           = (X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['77', '78'])).
% 9.71/9.89  thf('80', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.71/9.89          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 9.71/9.89      inference('demod', [status(thm)], ['51', '52'])).
% 9.71/9.89  thf('81', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 9.71/9.89          | ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1)
% 9.71/9.89              = (k3_xboole_0 @ X0 @ 
% 9.71/9.89                 (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))))),
% 9.71/9.89      inference('sup-', [status(thm)], ['79', '80'])).
% 9.71/9.89  thf('82', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1))
% 9.71/9.89           = (X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['77', '78'])).
% 9.71/9.89  thf('83', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 9.71/9.89          | ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1) = (X0)))),
% 9.71/9.89      inference('demod', [status(thm)], ['81', '82'])).
% 9.71/9.89  thf('84', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 9.71/9.89          | ((k2_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ X0) = (sk_A)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['74', '83'])).
% 9.71/9.89  thf('85', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['54', '55'])).
% 9.71/9.89  thf('86', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 9.71/9.89          | ((k2_xboole_0 @ sk_C @ X0) = (sk_A)))),
% 9.71/9.89      inference('demod', [status(thm)], ['84', '85'])).
% 9.71/9.89  thf('87', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ sk_C @ sk_A)
% 9.71/9.89          | ((k2_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_A)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['73', '86'])).
% 9.71/9.89  thf('88', plain,
% 9.71/9.89      (![X0 : $i]: ((k2_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['71', '72'])).
% 9.71/9.89  thf('89', plain, ((~ (r1_tarski @ sk_C @ sk_A) | ((sk_C) = (sk_A)))),
% 9.71/9.89      inference('demod', [status(thm)], ['87', '88'])).
% 9.71/9.89  thf('90', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('91', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 9.71/9.89      inference('split', [status(esa)], ['90'])).
% 9.71/9.89  thf('92', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 9.71/9.89      inference('sup-', [status(thm)], ['38', '53'])).
% 9.71/9.89  thf('93', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['42', '43'])).
% 9.71/9.89  thf('94', plain,
% 9.71/9.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('95', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['46', '47'])).
% 9.71/9.89  thf('96', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 9.71/9.89          (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['94', '95'])).
% 9.71/9.89  thf('97', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ 
% 9.71/9.89          (k2_zfmisc_1 @ X0 @ X1))),
% 9.71/9.89      inference('sup+', [status(thm)], ['93', '96'])).
% 9.71/9.89  thf('98', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_C @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['92', '97'])).
% 9.71/9.89  thf('99', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('100', plain,
% 9.71/9.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.71/9.89         (((X15) = (k1_xboole_0))
% 9.71/9.89          | (r1_tarski @ X16 @ X17)
% 9.71/9.89          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 9.71/9.89               (k2_zfmisc_1 @ X15 @ X17)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 9.71/9.89  thf('101', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_B)
% 9.71/9.89          | ((sk_A) = (k1_xboole_0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['99', '100'])).
% 9.71/9.89  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('103', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_B))),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 9.71/9.89  thf('104', plain, ((r1_tarski @ sk_D @ sk_B)),
% 9.71/9.89      inference('sup-', [status(thm)], ['98', '103'])).
% 9.71/9.89  thf('105', plain,
% 9.71/9.89      (![X5 : $i, X7 : $i]:
% 9.71/9.89         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 9.71/9.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.71/9.89  thf('106', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['104', '105'])).
% 9.71/9.89  thf('107', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['18', '19'])).
% 9.71/9.89  thf('108', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 9.71/9.89           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['40', '41'])).
% 9.71/9.89  thf('109', plain,
% 9.71/9.89      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['107', '108'])).
% 9.71/9.89  thf('110', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 9.71/9.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 9.71/9.89  thf('111', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['109', '110'])).
% 9.71/9.89  thf('112', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 9.71/9.89      inference('demod', [status(thm)], ['109', '110'])).
% 9.71/9.89  thf('113', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 9.71/9.89           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['23', '24'])).
% 9.71/9.89  thf('114', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 9.71/9.89         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['112', '113'])).
% 9.71/9.89  thf('115', plain,
% 9.71/9.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('116', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 9.71/9.89           (k3_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 9.71/9.89              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['114', '115'])).
% 9.71/9.89  thf('117', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('118', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 9.71/9.89           (k3_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 9.71/9.89      inference('demod', [status(thm)], ['116', '117'])).
% 9.71/9.89  thf('119', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 9.71/9.89      inference('sup-', [status(thm)], ['38', '53'])).
% 9.71/9.89  thf('120', plain,
% 9.71/9.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('121', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('122', plain,
% 9.71/9.89      (![X18 : $i, X20 : $i, X21 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X21 @ X20)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('123', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89              (k2_zfmisc_1 @ sk_A @ X0)))),
% 9.71/9.89      inference('sup+', [status(thm)], ['121', '122'])).
% 9.71/9.89  thf('124', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D))
% 9.71/9.89         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['120', '123'])).
% 9.71/9.89  thf('125', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('126', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['124', '125'])).
% 9.71/9.89  thf('127', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['54', '55'])).
% 9.71/9.89  thf('128', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B))
% 9.71/9.89         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['126', '127'])).
% 9.71/9.89  thf('129', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_B))),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 9.71/9.89  thf('130', plain,
% 9.71/9.89      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89           (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89        | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B))),
% 9.71/9.89      inference('sup-', [status(thm)], ['128', '129'])).
% 9.71/9.89  thf('131', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.71/9.89      inference('simplify', [status(thm)], ['36'])).
% 9.71/9.89  thf('132', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B)),
% 9.71/9.89      inference('demod', [status(thm)], ['130', '131'])).
% 9.71/9.89  thf('133', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.71/9.89          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['48', '49'])).
% 9.71/9.89  thf('134', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 9.71/9.89      inference('sup-', [status(thm)], ['132', '133'])).
% 9.71/9.89  thf('135', plain,
% 9.71/9.89      (![X8 : $i, X9 : $i]:
% 9.71/9.89         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 9.71/9.89      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.71/9.89  thf('136', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['134', '135'])).
% 9.71/9.89  thf('137', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['134', '135'])).
% 9.71/9.89  thf('138', plain,
% 9.71/9.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.71/9.89           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.71/9.89              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.71/9.89  thf('139', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('140', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.71/9.89         ((k2_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X2 @ X0))
% 9.71/9.89           = (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 9.71/9.89      inference('sup+', [status(thm)], ['138', '139'])).
% 9.71/9.89  thf('141', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         ((k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_D)
% 9.71/9.89           = (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['118', '119', '136', '137', '140'])).
% 9.71/9.89  thf('142', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_D)
% 9.71/9.89         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D))),
% 9.71/9.89      inference('sup+', [status(thm)], ['111', '141'])).
% 9.71/9.89  thf('143', plain,
% 9.71/9.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.71/9.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.71/9.89  thf('144', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 9.71/9.89      inference('sup+', [status(thm)], ['54', '55'])).
% 9.71/9.89  thf('145', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['142', '143', '144'])).
% 9.71/9.89  thf('146', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('147', plain,
% 9.71/9.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.71/9.89         (((X15) = (k1_xboole_0))
% 9.71/9.89          | (r1_tarski @ X16 @ X17)
% 9.71/9.89          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 9.71/9.89               (k2_zfmisc_1 @ X15 @ X17)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 9.71/9.89  thf('148', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_A @ X0))
% 9.71/9.89          | (r1_tarski @ sk_B @ X0)
% 9.71/9.89          | ((sk_A) = (k1_xboole_0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['146', '147'])).
% 9.71/9.89  thf('149', plain, (((sk_A) != (k1_xboole_0))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('150', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_A @ X0))
% 9.71/9.89          | (r1_tarski @ sk_B @ X0))),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 9.71/9.89  thf('151', plain,
% 9.71/9.89      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 9.71/9.89           (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89        | (r1_tarski @ sk_B @ sk_D))),
% 9.71/9.89      inference('sup-', [status(thm)], ['145', '150'])).
% 9.71/9.89  thf('152', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.71/9.89      inference('simplify', [status(thm)], ['36'])).
% 9.71/9.89  thf('153', plain, ((r1_tarski @ sk_B @ sk_D)),
% 9.71/9.89      inference('demod', [status(thm)], ['151', '152'])).
% 9.71/9.89  thf('154', plain, (((sk_B) = (sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['106', '153'])).
% 9.71/9.89  thf('155', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 9.71/9.89      inference('split', [status(esa)], ['90'])).
% 9.71/9.89  thf('156', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 9.71/9.89      inference('sup-', [status(thm)], ['154', '155'])).
% 9.71/9.89  thf('157', plain, ((((sk_B) = (sk_D)))),
% 9.71/9.89      inference('simplify', [status(thm)], ['156'])).
% 9.71/9.89  thf('158', plain, (~ (((sk_A) = (sk_C))) | ~ (((sk_B) = (sk_D)))),
% 9.71/9.89      inference('split', [status(esa)], ['90'])).
% 9.71/9.89  thf('159', plain, (~ (((sk_A) = (sk_C)))),
% 9.71/9.89      inference('sat_resolution*', [status(thm)], ['157', '158'])).
% 9.71/9.89  thf('160', plain, (((sk_A) != (sk_C))),
% 9.71/9.89      inference('simpl_trail', [status(thm)], ['91', '159'])).
% 9.71/9.89  thf('161', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['89', '160'])).
% 9.71/9.89  thf('162', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.71/9.89      inference('simplify', [status(thm)], ['36'])).
% 9.71/9.89  thf('163', plain,
% 9.71/9.89      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('164', plain,
% 9.71/9.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.71/9.89         (((X15) = (k1_xboole_0))
% 9.71/9.89          | (r1_tarski @ X16 @ X17)
% 9.71/9.89          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 9.71/9.89               (k2_zfmisc_1 @ X17 @ X15)))),
% 9.71/9.89      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 9.71/9.89  thf('165', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_A)
% 9.71/9.89          | ((sk_B) = (k1_xboole_0)))),
% 9.71/9.89      inference('sup-', [status(thm)], ['163', '164'])).
% 9.71/9.89  thf('166', plain, (((sk_B) != (k1_xboole_0))),
% 9.71/9.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.71/9.89  thf('167', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_A))),
% 9.71/9.89      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 9.71/9.89  thf('168', plain, (((sk_B) = (sk_D))),
% 9.71/9.89      inference('demod', [status(thm)], ['106', '153'])).
% 9.71/9.89  thf('169', plain,
% 9.71/9.89      (![X0 : $i]:
% 9.71/9.89         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 9.71/9.89             (k2_zfmisc_1 @ sk_C @ sk_D))
% 9.71/9.89          | (r1_tarski @ X0 @ sk_A))),
% 9.71/9.89      inference('demod', [status(thm)], ['167', '168'])).
% 9.71/9.89  thf('170', plain, ((r1_tarski @ sk_C @ sk_A)),
% 9.71/9.89      inference('sup-', [status(thm)], ['162', '169'])).
% 9.71/9.89  thf('171', plain, ($false), inference('demod', [status(thm)], ['161', '170'])).
% 9.71/9.89  
% 9.71/9.89  % SZS output end Refutation
% 9.71/9.89  
% 9.71/9.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
