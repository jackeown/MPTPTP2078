%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyd8Bq1qjp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 (1212 expanded)
%              Number of leaves         :   26 ( 410 expanded)
%              Depth                    :   24
%              Number of atoms          : 1004 (9923 expanded)
%              Number of equality atoms :  105 ( 770 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('23',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X50 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','47'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      = ( k5_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['50','59'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['75','101'])).

thf('103',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['50','59'])).

thf('104',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('106',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['74','104','105'])).

thf('107',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyd8Bq1qjp
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 389 iterations in 0.128s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.59  thf('0', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.59  thf(t100_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.59  thf(t36_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.22/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.59  thf(t28_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.22/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.59  thf(t79_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.22/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.59  thf(t4_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X3 : $i, X4 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X3 @ X4)
% 0.22/0.59          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.59          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.59  thf('13', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['8', '13'])).
% 0.22/0.59  thf(t7_xboole_0, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('15', plain,
% 0.22/0.59      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.22/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.59  thf('16', plain,
% 0.22/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.59  thf('18', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.59  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['7', '18'])).
% 0.22/0.59  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.22/0.59  thf(t98_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (![X20 : $i, X21 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ X20 @ X21)
% 0.22/0.59           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.59  thf(t46_zfmisc_1, conjecture,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.59       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i,B:$i]:
% 0.22/0.59        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.59          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.22/0.59  thf('22', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(l1_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      (![X50 : $i, X52 : $i]:
% 0.22/0.59         ((r1_tarski @ (k1_tarski @ X50) @ X52) | ~ (r2_hidden @ X50 @ X52))),
% 0.22/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.59  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.22/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.59  thf('26', plain,
% 0.22/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.59  thf(t91_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ X0)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.59           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['21', '32'])).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.59         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.22/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      ((r1_tarski @ 
% 0.22/0.59        (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) @ 
% 0.22/0.59        (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.59  thf('39', plain,
% 0.22/0.59      (((k3_xboole_0 @ 
% 0.22/0.59         (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) @ 
% 0.22/0.59         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.59         (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.59  thf('42', plain,
% 0.22/0.59      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.59         (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.59  thf('43', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.59  thf('44', plain,
% 0.22/0.59      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.22/0.59         (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.22/0.59         = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.59  thf('45', plain,
% 0.22/0.59      (((k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.59         = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['41', '44'])).
% 0.22/0.59  thf('46', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('47', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ 
% 0.22/0.59              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.59         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['20', '47'])).
% 0.22/0.59  thf(t5_boole, axiom,
% 0.22/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.59  thf('49', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('50', plain,
% 0.22/0.59      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.59  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['7', '18'])).
% 0.22/0.59  thf('52', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.59  thf('53', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('54', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.59           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.59  thf('55', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('56', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.59  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['51', '56'])).
% 0.22/0.59  thf('58', plain,
% 0.22/0.59      (![X20 : $i, X21 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ X20 @ X21)
% 0.22/0.59           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.59  thf('59', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('60', plain,
% 0.22/0.59      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['50', '59'])).
% 0.22/0.59  thf('61', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('62', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('63', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ X0 @ X1)
% 0.22/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['61', '62'])).
% 0.22/0.59  thf('64', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('65', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ X0 @ X1)
% 0.22/0.59           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.22/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.59  thf('66', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.59           = (k5_xboole_0 @ X0 @ sk_B_1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['60', '65'])).
% 0.22/0.59  thf('67', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.22/0.59  thf('68', plain,
% 0.22/0.59      (((k1_xboole_0)
% 0.22/0.59         = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ sk_B_1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['66', '67'])).
% 0.22/0.59  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.22/0.59  thf('70', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('71', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['69', '70'])).
% 0.22/0.59  thf('72', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('73', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.22/0.59  thf('74', plain,
% 0.22/0.59      (((k2_xboole_0 @ k1_xboole_0 @ sk_B_1)
% 0.22/0.59         = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ 
% 0.22/0.59            k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['68', '73'])).
% 0.22/0.59  thf('75', plain,
% 0.22/0.59      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['50', '59'])).
% 0.22/0.59  thf('76', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('77', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ 
% 0.22/0.59              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.59  thf('78', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('79', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ 
% 0.22/0.59              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.59  thf('80', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('81', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ 
% 0.22/0.59              (k5_xboole_0 @ 
% 0.22/0.59               (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0) @ 
% 0.22/0.59               X1)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['79', '80'])).
% 0.22/0.59  thf('82', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.22/0.59           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('83', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ sk_B_1 @ 
% 0.22/0.59              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ X0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.59  thf('84', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1)
% 0.22/0.59           = (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.22/0.59      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.22/0.59  thf('85', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.22/0.59           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['76', '84'])).
% 0.22/0.59  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['7', '18'])).
% 0.22/0.59  thf('87', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.59  thf('88', plain,
% 0.22/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['86', '87'])).
% 0.22/0.59  thf('89', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('90', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('91', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('92', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['88', '91'])).
% 0.22/0.59  thf('93', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.22/0.59  thf('94', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.59      inference('demod', [status(thm)], ['92', '93'])).
% 0.22/0.59  thf('95', plain,
% 0.22/0.59      (![X20 : $i, X21 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ X20 @ X21)
% 0.22/0.59           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.59  thf('96', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['94', '95'])).
% 0.22/0.59  thf('97', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('98', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['96', '97'])).
% 0.22/0.59  thf('99', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['85', '98'])).
% 0.22/0.59  thf('100', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('101', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.59           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.59  thf('102', plain,
% 0.22/0.59      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.59         = (k2_xboole_0 @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['75', '101'])).
% 0.22/0.59  thf('103', plain,
% 0.22/0.59      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59         (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['50', '59'])).
% 0.22/0.59  thf('104', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B_1) = (sk_B_1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['102', '103'])).
% 0.22/0.59  thf('105', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('106', plain, (((sk_B_1) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['74', '104', '105'])).
% 0.22/0.59  thf('107', plain,
% 0.22/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('108', plain, ($false),
% 0.22/0.59      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.22/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
