%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1WdPGhecp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 247 expanded)
%              Number of leaves         :   22 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  739 (1911 expanded)
%              Number of equality atoms :   68 ( 190 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('26',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','40'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['4','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1WdPGhecp
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.72/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.96  % Solved by: fo/fo7.sh
% 0.72/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.96  % done 1035 iterations in 0.454s
% 0.72/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.96  % SZS output start Refutation
% 0.72/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.72/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.96  thf(t48_xboole_1, conjecture,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.96    (~( ![A:$i,B:$i]:
% 0.72/0.96        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.72/0.96          ( k3_xboole_0 @ A @ B ) ) )),
% 0.72/0.96    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.72/0.96  thf('0', plain,
% 0.72/0.96      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.72/0.96         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.72/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.96  thf(t47_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.72/0.96  thf('1', plain,
% 0.72/0.96      (![X27 : $i, X28 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 0.72/0.96           = (k4_xboole_0 @ X27 @ X28))),
% 0.72/0.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.96  thf(t39_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.72/0.96  thf('2', plain,
% 0.72/0.96      (![X23 : $i, X24 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.72/0.96           = (k2_xboole_0 @ X23 @ X24))),
% 0.72/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.96  thf(t40_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.72/0.96  thf('3', plain,
% 0.72/0.96      (![X25 : $i, X26 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 0.72/0.96           = (k4_xboole_0 @ X25 @ X26))),
% 0.72/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.72/0.96  thf('4', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.72/0.96           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.72/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.72/0.96  thf(t3_xboole_0, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.72/0.96            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.96       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.96            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.72/0.96  thf('5', plain,
% 0.72/0.96      (![X8 : $i, X9 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.72/0.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.96  thf('6', plain,
% 0.72/0.96      (![X8 : $i, X9 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.72/0.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.96  thf(d5_xboole_0, axiom,
% 0.72/0.96    (![A:$i,B:$i,C:$i]:
% 0.72/0.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.72/0.96       ( ![D:$i]:
% 0.72/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.72/0.96  thf('7', plain,
% 0.72/0.96      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X6 @ X5)
% 0.72/0.96          | ~ (r2_hidden @ X6 @ X4)
% 0.72/0.96          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.72/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.72/0.96  thf('8', plain,
% 0.72/0.96      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X6 @ X4)
% 0.72/0.96          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.72/0.96      inference('simplify', [status(thm)], ['7'])).
% 0.72/0.96  thf('9', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.72/0.96          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['6', '8'])).
% 0.72/0.96  thf('10', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.72/0.96          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['5', '9'])).
% 0.72/0.96  thf('11', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.72/0.96      inference('simplify', [status(thm)], ['10'])).
% 0.72/0.96  thf('12', plain,
% 0.72/0.96      (![X8 : $i, X9 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.72/0.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.96  thf('13', plain,
% 0.72/0.96      (![X8 : $i, X9 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.72/0.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.96  thf('14', plain,
% 0.72/0.96      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X10 @ X8)
% 0.72/0.96          | ~ (r2_hidden @ X10 @ X11)
% 0.72/0.96          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.72/0.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.96  thf('15', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X1 @ X0)
% 0.72/0.96          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.72/0.96          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.72/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.96  thf('16', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((r1_xboole_0 @ X0 @ X1)
% 0.72/0.96          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.72/0.96          | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup-', [status(thm)], ['12', '15'])).
% 0.72/0.96  thf('17', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('simplify', [status(thm)], ['16'])).
% 0.72/0.96  thf('18', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['11', '17'])).
% 0.72/0.96  thf('19', plain,
% 0.72/0.96      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.72/0.96         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.72/0.96          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.72/0.96          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.72/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.72/0.96  thf(t36_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.72/0.96  thf('20', plain,
% 0.72/0.96      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.72/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.72/0.96  thf(l32_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.96  thf('21', plain,
% 0.72/0.96      (![X16 : $i, X18 : $i]:
% 0.72/0.96         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.72/0.96          | ~ (r1_tarski @ X16 @ X18))),
% 0.72/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.96  thf('22', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.96  thf('23', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.96  thf('24', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['22', '23'])).
% 0.72/0.96  thf('25', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.96  thf('26', plain,
% 0.72/0.96      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.96  thf('27', plain,
% 0.72/0.96      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X6 @ X4)
% 0.72/0.96          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.72/0.96      inference('simplify', [status(thm)], ['7'])).
% 0.72/0.96  thf('28', plain,
% 0.72/0.96      (![X0 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.96  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.72/0.96      inference('simplify', [status(thm)], ['28'])).
% 0.72/0.96  thf('30', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.72/0.96          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.72/0.96      inference('sup-', [status(thm)], ['19', '29'])).
% 0.72/0.96  thf('31', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.96  thf('32', plain,
% 0.72/0.96      (![X23 : $i, X24 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.72/0.96           = (k2_xboole_0 @ X23 @ X24))),
% 0.72/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.96  thf('33', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.72/0.96           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.96      inference('sup+', [status(thm)], ['31', '32'])).
% 0.72/0.96  thf(commutativity_k2_xboole_0, axiom,
% 0.72/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.72/0.96  thf('34', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.96  thf('35', plain,
% 0.72/0.96      (![X25 : $i, X26 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 0.72/0.96           = (k4_xboole_0 @ X25 @ X26))),
% 0.72/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.72/0.96  thf('36', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.72/0.96  thf('37', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.72/0.96           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['33', '36'])).
% 0.72/0.96  thf('38', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.72/0.96  thf('39', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.96  thf('40', plain,
% 0.72/0.96      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.72/0.96  thf('41', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.72/0.96          | ((X1) = (k1_xboole_0)))),
% 0.72/0.96      inference('demod', [status(thm)], ['30', '40'])).
% 0.72/0.96  thf(t4_xboole_0, axiom,
% 0.72/0.96    (![A:$i,B:$i]:
% 0.72/0.96     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.96            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.96       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.96            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.72/0.96  thf('42', plain,
% 0.72/0.96      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.72/0.96         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.72/0.96          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.72/0.96      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.72/0.96  thf('43', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['41', '42'])).
% 0.72/0.96  thf('44', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.72/0.96      inference('sup-', [status(thm)], ['18', '43'])).
% 0.72/0.96  thf('45', plain,
% 0.72/0.96      (![X27 : $i, X28 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28))
% 0.72/0.96           = (k4_xboole_0 @ X27 @ X28))),
% 0.72/0.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.72/0.96  thf('46', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.96      inference('sup+', [status(thm)], ['44', '45'])).
% 0.72/0.96  thf('47', plain,
% 0.72/0.96      (![X23 : $i, X24 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.72/0.96           = (k2_xboole_0 @ X23 @ X24))),
% 0.72/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.96  thf(t22_xboole_1, axiom,
% 0.72/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.72/0.96  thf('48', plain,
% 0.72/0.96      (![X19 : $i, X20 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)) = (X19))),
% 0.72/0.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.72/0.96  thf('49', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.72/0.96  thf('50', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ X0 @ X0)
% 0.72/0.96           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['48', '49'])).
% 0.72/0.96  thf('51', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.72/0.96           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.96      inference('sup+', [status(thm)], ['31', '32'])).
% 0.72/0.96  thf('52', plain,
% 0.72/0.96      (![X23 : $i, X24 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.72/0.96           = (k2_xboole_0 @ X23 @ X24))),
% 0.72/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.96  thf('53', plain,
% 0.72/0.96      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['51', '52'])).
% 0.72/0.96  thf('54', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.72/0.96  thf('55', plain,
% 0.72/0.96      (![X0 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.96  thf('56', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.72/0.96  thf('57', plain,
% 0.72/0.96      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.72/0.96      inference('demod', [status(thm)], ['55', '56'])).
% 0.72/0.96  thf('58', plain,
% 0.72/0.96      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.72/0.96      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.72/0.96  thf('59', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.72/0.96      inference('demod', [status(thm)], ['57', '58'])).
% 0.72/0.96  thf('60', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.72/0.96      inference('demod', [status(thm)], ['50', '59'])).
% 0.72/0.96  thf('61', plain,
% 0.72/0.96      (![X23 : $i, X24 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.72/0.96           = (k2_xboole_0 @ X23 @ X24))),
% 0.72/0.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.72/0.96  thf('62', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.72/0.96           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.72/0.96      inference('sup+', [status(thm)], ['60', '61'])).
% 0.72/0.96  thf('63', plain,
% 0.72/0.96      (![X19 : $i, X20 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)) = (X19))),
% 0.72/0.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.72/0.96  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['62', '63'])).
% 0.72/0.96  thf('65', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.96  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['64', '65'])).
% 0.72/0.96  thf('67', plain,
% 0.72/0.96      (![X0 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['47', '66'])).
% 0.72/0.96  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['64', '65'])).
% 0.72/0.96  thf('69', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.72/0.96      inference('demod', [status(thm)], ['67', '68'])).
% 0.72/0.96  thf('70', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.96      inference('demod', [status(thm)], ['46', '69'])).
% 0.72/0.96  thf('71', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.72/0.96           = (X1))),
% 0.72/0.96      inference('demod', [status(thm)], ['4', '70'])).
% 0.72/0.96  thf('72', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.72/0.96           (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.72/0.96      inference('sup+', [status(thm)], ['1', '71'])).
% 0.72/0.96  thf('73', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.96  thf('74', plain,
% 0.72/0.96      (![X19 : $i, X20 : $i]:
% 0.72/0.96         ((k2_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)) = (X19))),
% 0.72/0.96      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.72/0.96  thf('75', plain,
% 0.72/0.96      (![X0 : $i, X1 : $i]:
% 0.72/0.96         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.72/0.96           = (k3_xboole_0 @ X1 @ X0))),
% 0.72/0.96      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.72/0.96  thf('76', plain,
% 0.72/0.96      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.72/0.96      inference('demod', [status(thm)], ['0', '75'])).
% 0.72/0.96  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.72/0.96  
% 0.72/0.96  % SZS output end Refutation
% 0.72/0.96  
% 0.72/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
