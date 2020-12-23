%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iISbC09vkk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:35 EST 2020

% Result     : Theorem 34.81s
% Output     : Refutation 34.81s
% Verified   : 
% Statistics : Number of formulae       :  304 (3010 expanded)
%              Number of leaves         :   26 ( 876 expanded)
%              Depth                    :   42
%              Number of atoms          : 2561 (28531 expanded)
%              Number of equality atoms :  293 (2830 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_xboole_0 @ X18 @ X20 )
      | ( X18 = X20 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_zfmisc_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','54'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_xboole_0 @ X22 @ X23 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('68',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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

thf('72',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('74',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X1 @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ X0 ) @ sk_D_2 )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2 )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_3 ) @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_zfmisc_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_3 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_3 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('86',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_3 ) )
    | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['86','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ sk_C_3 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['57','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('105',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('107',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ) ) ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('111',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['104','117'])).

thf('119',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('122',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['122','125','126'])).

thf('128',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['103','127'])).

thf('129',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('131',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['131','132','133'])).

thf('135',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['128','134'])).

thf('136',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('137',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('138',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['136','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['135','144'])).

thf('146',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 != X19 )
      | ~ ( r2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('147',plain,(
    ! [X19: $i] :
      ~ ( r2_xboole_0 @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    r1_tarski @ sk_A @ sk_C_3 ),
    inference(clc,[status(thm)],['145','147'])).

thf('149',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('150',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_3 )
    = sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('157',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('159',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['160','163'])).

thf('165',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['150','151'])).

thf('167',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('169',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X1 @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_C_3 @ ( k3_xboole_0 @ sk_D_2 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_C_3 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_D_2 ) @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D_2 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D_2 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('184',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) )
    | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ X0 ) @ sk_D_2 )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('186',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2 )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('188',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('189',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('194',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('196',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ sk_D_2 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['173','200'])).

thf('202',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['122','125','126'])).

thf('203',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['131','132','133'])).

thf('205',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('207',plain,
    ( ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X19: $i] :
      ~ ( r2_xboole_0 @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('209',plain,(
    r1_tarski @ sk_B @ sk_D_2 ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('211',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('213',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ sk_D_2 ) ),
    inference(demod,[status(thm)],['169','170','171','172','213'])).

thf('215',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D_2 )
    = ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('219',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_D_2 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) ) ) ),
    inference('sup+',[status(thm)],['216','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_D_2 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ X0 ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ ( k4_xboole_0 @ X0 @ sk_A ) ) @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['154','222'])).

thf('224',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('225',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_3 @ ( k4_xboole_0 @ X0 @ sk_A ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_3 @ sk_A ) @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['153','225'])).

thf('227',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('228',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_3 @ sk_A )
      = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( sk_D_2 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_3 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_3 @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('234',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X35 @ X37 ) @ ( k3_xboole_0 @ X36 @ X38 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X35 @ X36 ) @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('237',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_D_2 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['232','237'])).

thf('239',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['150','151'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_D_2 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_D_2 )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_D_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['231','242'])).

thf('244',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D_2 @ ( k4_xboole_0 @ X0 @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D_2 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('249',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('251',plain,
    ( ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_D_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X19: $i] :
      ~ ( r2_xboole_0 @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('253',plain,(
    r1_tarski @ sk_D_2 @ sk_B ),
    inference(clc,[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('255',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( ( k3_xboole_0 @ sk_D_2 @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['211','212'])).

thf('257',plain,(
    sk_D_2 = sk_B ),
    inference('sup+',[status(thm)],['255','256'])).

thf('258',plain,(
    sk_D_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['230','257'])).

thf('259',plain,
    ( ( k4_xboole_0 @ sk_C_3 @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['229','258'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('261',plain,
    ( ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X19: $i] :
      ~ ( r2_xboole_0 @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('263',plain,(
    r1_tarski @ sk_C_3 @ sk_A ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('265',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_A )
    = sk_C_3 ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    sk_A = sk_C_3 ),
    inference('sup+',[status(thm)],['152','265'])).

thf('267',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B != sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['267'])).

thf('269',plain,(
    sk_D_2 = sk_B ),
    inference('sup+',[status(thm)],['255','256'])).

thf('270',plain,
    ( ( sk_B != sk_D_2 )
   <= ( sk_B != sk_D_2 ) ),
    inference(split,[status(esa)],['267'])).

thf('271',plain,
    ( ( sk_D_2 != sk_D_2 )
   <= ( sk_B != sk_D_2 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    sk_B = sk_D_2 ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( sk_A != sk_C_3 )
    | ( sk_B != sk_D_2 ) ),
    inference(split,[status(esa)],['267'])).

thf('274',plain,(
    sk_A != sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['272','273'])).

thf('275',plain,(
    sk_A != sk_C_3 ),
    inference(simpl_trail,[status(thm)],['268','274'])).

thf('276',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['266','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iISbC09vkk
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 34.81/35.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 34.81/35.03  % Solved by: fo/fo7.sh
% 34.81/35.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.81/35.03  % done 16727 iterations in 34.535s
% 34.81/35.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 34.81/35.03  % SZS output start Refutation
% 34.81/35.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.81/35.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 34.81/35.03  thf(sk_A_type, type, sk_A: $i).
% 34.81/35.03  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 34.81/35.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 34.81/35.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 34.81/35.03  thf(sk_C_3_type, type, sk_C_3: $i).
% 34.81/35.03  thf(sk_B_type, type, sk_B: $i).
% 34.81/35.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 34.81/35.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 34.81/35.03  thf(sk_D_2_type, type, sk_D_2: $i).
% 34.81/35.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 34.81/35.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 34.81/35.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 34.81/35.03  thf(d3_tarski, axiom,
% 34.81/35.03    (![A:$i,B:$i]:
% 34.81/35.03     ( ( r1_tarski @ A @ B ) <=>
% 34.81/35.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 34.81/35.03  thf('0', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('1', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf(t4_boole, axiom,
% 34.81/35.03    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 34.81/35.03  thf('2', plain,
% 34.81/35.03      (![X26 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [t4_boole])).
% 34.81/35.03  thf(d5_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i,C:$i]:
% 34.81/35.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 34.81/35.03       ( ![D:$i]:
% 34.81/35.03         ( ( r2_hidden @ D @ C ) <=>
% 34.81/35.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 34.81/35.03  thf('3', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X16 @ X15)
% 34.81/35.03          | ~ (r2_hidden @ X16 @ X14)
% 34.81/35.03          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 34.81/35.03  thf('4', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X16 @ X14)
% 34.81/35.03          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['3'])).
% 34.81/35.03  thf('5', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['2', '4'])).
% 34.81/35.03  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 34.81/35.03      inference('sup-', [status(thm)], ['1', '6'])).
% 34.81/35.03  thf(t28_xboole_1, axiom,
% 34.81/35.03    (![A:$i,B:$i]:
% 34.81/35.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 34.81/35.03  thf('8', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('9', plain,
% 34.81/35.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['7', '8'])).
% 34.81/35.03  thf('10', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf(d4_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i,C:$i]:
% 34.81/35.03     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 34.81/35.03       ( ![D:$i]:
% 34.81/35.03         ( ( r2_hidden @ D @ C ) <=>
% 34.81/35.03           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 34.81/35.03  thf('11', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X10 @ X9)
% 34.81/35.03          | (r2_hidden @ X10 @ X8)
% 34.81/35.03          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 34.81/35.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.81/35.03  thf('12', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X10 : $i]:
% 34.81/35.03         ((r2_hidden @ X10 @ X8)
% 34.81/35.03          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['11'])).
% 34.81/35.03  thf('13', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 34.81/35.03          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['10', '12'])).
% 34.81/35.03  thf('14', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('15', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 34.81/35.03          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['13', '14'])).
% 34.81/35.03  thf('16', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['15'])).
% 34.81/35.03  thf(d8_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i]:
% 34.81/35.03     ( ( r2_xboole_0 @ A @ B ) <=>
% 34.81/35.03       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 34.81/35.03  thf('17', plain,
% 34.81/35.03      (![X18 : $i, X20 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ X18 @ X20)
% 34.81/35.03          | ((X18) = (X20))
% 34.81/35.03          | ~ (r1_tarski @ X18 @ X20))),
% 34.81/35.03      inference('cnf', [status(esa)], [d8_xboole_0])).
% 34.81/35.03  thf('18', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 34.81/35.03          | (r2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['16', '17'])).
% 34.81/35.03  thf('19', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ k1_xboole_0 @ X0)
% 34.81/35.03          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['9', '18'])).
% 34.81/35.03  thf('20', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X10 @ X9)
% 34.81/35.03          | (r2_hidden @ X10 @ X7)
% 34.81/35.03          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 34.81/35.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.81/35.03  thf('21', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X10 : $i]:
% 34.81/35.03         ((r2_hidden @ X10 @ X7)
% 34.81/35.03          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['20'])).
% 34.81/35.03  thf('22', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X1 @ X0)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ X0)
% 34.81/35.03          | (r2_hidden @ X1 @ k1_xboole_0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['19', '21'])).
% 34.81/35.03  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('24', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 34.81/35.03      inference('clc', [status(thm)], ['22', '23'])).
% 34.81/35.03  thf('25', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ X0 @ X1) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['0', '24'])).
% 34.81/35.03  thf('26', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('27', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ k1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['25', '26'])).
% 34.81/35.03  thf('28', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('29', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X16 @ X15)
% 34.81/35.03          | (r2_hidden @ X16 @ X13)
% 34.81/35.03          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 34.81/35.03  thf('30', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 34.81/35.03         ((r2_hidden @ X16 @ X13)
% 34.81/35.03          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['29'])).
% 34.81/35.03  thf('31', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 34.81/35.03          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 34.81/35.03      inference('sup-', [status(thm)], ['28', '30'])).
% 34.81/35.03  thf('32', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('33', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 34.81/35.03          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['31', '32'])).
% 34.81/35.03  thf('34', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['33'])).
% 34.81/35.03  thf('35', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('36', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('sup-', [status(thm)], ['34', '35'])).
% 34.81/35.03  thf(commutativity_k3_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 34.81/35.03  thf('37', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('38', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('demod', [status(thm)], ['36', '37'])).
% 34.81/35.03  thf('39', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((X0) = (k4_xboole_0 @ X0 @ X1)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['27', '38'])).
% 34.81/35.03  thf('40', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 34.81/35.03          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 34.81/35.03      inference('sup-', [status(thm)], ['28', '30'])).
% 34.81/35.03  thf('41', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('42', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X16 @ X14)
% 34.81/35.03          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['3'])).
% 34.81/35.03  thf('43', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 34.81/35.03          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['41', '42'])).
% 34.81/35.03  thf('44', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 34.81/35.03          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 34.81/35.03      inference('sup-', [status(thm)], ['40', '43'])).
% 34.81/35.03  thf('45', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 34.81/35.03      inference('simplify', [status(thm)], ['44'])).
% 34.81/35.03  thf('46', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('47', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 34.81/35.03           = (k4_xboole_0 @ X1 @ X1))),
% 34.81/35.03      inference('sup-', [status(thm)], ['45', '46'])).
% 34.81/35.03  thf('48', plain,
% 34.81/35.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['7', '8'])).
% 34.81/35.03  thf('49', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('50', plain,
% 34.81/35.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['48', '49'])).
% 34.81/35.03  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['47', '50'])).
% 34.81/35.03  thf(t113_zfmisc_1, axiom,
% 34.81/35.03    (![A:$i,B:$i]:
% 34.81/35.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 34.81/35.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 34.81/35.03  thf('52', plain,
% 34.81/35.03      (![X33 : $i, X34 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X33 @ X34) = (k1_xboole_0))
% 34.81/35.03          | ((X34) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('53', plain,
% 34.81/35.03      (![X33 : $i]: ((k2_zfmisc_1 @ X33 @ k1_xboole_0) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['52'])).
% 34.81/35.03  thf('54', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['51', '53'])).
% 34.81/35.03  thf('55', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['39', '54'])).
% 34.81/35.03  thf(t6_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i]:
% 34.81/35.03     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 34.81/35.03          ( ![C:$i]:
% 34.81/35.03            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 34.81/35.03  thf('56', plain,
% 34.81/35.03      (![X22 : $i, X23 : $i]:
% 34.81/35.03         (~ (r2_xboole_0 @ X22 @ X23)
% 34.81/35.03          | (r2_hidden @ (sk_C_1 @ X23 @ X22) @ X23))),
% 34.81/35.03      inference('cnf', [status(esa)], [t6_xboole_0])).
% 34.81/35.03  thf('57', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 34.81/35.03          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['55', '56'])).
% 34.81/35.03  thf('58', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X11 : $i]:
% 34.81/35.03         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 34.81/35.03          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 34.81/35.03          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 34.81/35.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.81/35.03  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('60', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 34.81/35.03          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['58', '59'])).
% 34.81/35.03  thf('61', plain,
% 34.81/35.03      (![X7 : $i, X8 : $i, X11 : $i]:
% 34.81/35.03         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 34.81/35.03          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 34.81/35.03          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 34.81/35.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.81/35.03  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('63', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 34.81/35.03          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['61', '62'])).
% 34.81/35.03  thf('64', plain,
% 34.81/35.03      (![X13 : $i, X14 : $i, X16 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X16 @ X14)
% 34.81/35.03          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['3'])).
% 34.81/35.03  thf('65', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         (((k1_xboole_0) = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 34.81/35.03          | ~ (r2_hidden @ 
% 34.81/35.03               (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['63', '64'])).
% 34.81/35.03  thf('66', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 34.81/35.03          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 34.81/35.03      inference('sup-', [status(thm)], ['60', '65'])).
% 34.81/35.03  thf('67', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['66'])).
% 34.81/35.03  thf(idempotence_k3_xboole_0, axiom,
% 34.81/35.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 34.81/35.03  thf('68', plain, (![X21 : $i]: ((k3_xboole_0 @ X21 @ X21) = (X21))),
% 34.81/35.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 34.81/35.03  thf(t123_zfmisc_1, axiom,
% 34.81/35.03    (![A:$i,B:$i,C:$i,D:$i]:
% 34.81/35.03     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 34.81/35.03       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 34.81/35.03  thf('69', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('70', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['68', '69'])).
% 34.81/35.03  thf('71', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf(t134_zfmisc_1, conjecture,
% 34.81/35.03    (![A:$i,B:$i,C:$i,D:$i]:
% 34.81/35.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 34.81/35.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 34.81/35.03         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 34.81/35.03  thf(zf_stmt_0, negated_conjecture,
% 34.81/35.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 34.81/35.03        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 34.81/35.03          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 34.81/35.03            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 34.81/35.03    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 34.81/35.03  thf('72', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('73', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('74', plain,
% 34.81/35.03      (![X32 : $i, X33 : $i]:
% 34.81/35.03         (((X32) = (k1_xboole_0))
% 34.81/35.03          | ((X33) = (k1_xboole_0))
% 34.81/35.03          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('75', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 34.81/35.03            != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['73', '74'])).
% 34.81/35.03  thf('76', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 34.81/35.03            (k2_zfmisc_1 @ sk_C_3 @ sk_D_2)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X1 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['72', '75'])).
% 34.81/35.03  thf('77', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03            (k2_zfmisc_1 @ X1 @ X0)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X1 @ sk_A) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['71', '76'])).
% 34.81/35.03  thf('78', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ X0) @ sk_D_2)
% 34.81/35.03            != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['70', '77'])).
% 34.81/35.03  thf('79', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_3) @ sk_A) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['67', '78'])).
% 34.81/35.03  thf('80', plain,
% 34.81/35.03      (![X33 : $i, X34 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X33 @ X34) = (k1_xboole_0))
% 34.81/35.03          | ((X33) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('81', plain,
% 34.81/35.03      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['80'])).
% 34.81/35.03  thf('82', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('83', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_3)) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('demod', [status(thm)], ['79', '81', '82'])).
% 34.81/35.03  thf('84', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_3)) = (k1_xboole_0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['83'])).
% 34.81/35.03  thf('85', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('demod', [status(thm)], ['36', '37'])).
% 34.81/35.03  thf('86', plain,
% 34.81/35.03      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3))
% 34.81/35.03        | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['84', '85'])).
% 34.81/35.03  thf('87', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('88', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['15'])).
% 34.81/35.03  thf('89', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('90', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 34.81/35.03           = (k3_xboole_0 @ X1 @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['88', '89'])).
% 34.81/35.03  thf('91', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('92', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 34.81/35.03           = (k3_xboole_0 @ X1 @ X0))),
% 34.81/35.03      inference('demod', [status(thm)], ['90', '91'])).
% 34.81/35.03  thf('93', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 34.81/35.03           = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('sup+', [status(thm)], ['87', '92'])).
% 34.81/35.03  thf('94', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['15'])).
% 34.81/35.03  thf('95', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('sup+', [status(thm)], ['93', '94'])).
% 34.81/35.03  thf('96', plain,
% 34.81/35.03      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_D_2) @ k1_xboole_0)
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['86', '95'])).
% 34.81/35.03  thf('97', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('98', plain,
% 34.81/35.03      (((r1_tarski @ (k3_xboole_0 @ sk_D_2 @ sk_B) @ k1_xboole_0)
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3)))),
% 34.81/35.03      inference('demod', [status(thm)], ['96', '97'])).
% 34.81/35.03  thf('99', plain,
% 34.81/35.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X2 @ X3)
% 34.81/35.03          | (r2_hidden @ X2 @ X4)
% 34.81/35.03          | ~ (r1_tarski @ X3 @ X4))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('100', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3))
% 34.81/35.03          | (r2_hidden @ X0 @ k1_xboole_0)
% 34.81/35.03          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['98', '99'])).
% 34.81/35.03  thf('101', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('102', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B))
% 34.81/35.03          | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3)))),
% 34.81/35.03      inference('clc', [status(thm)], ['100', '101'])).
% 34.81/35.03  thf('103', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B)) = (k1_xboole_0))
% 34.81/35.03          | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['57', '102'])).
% 34.81/35.03  thf('104', plain, (![X21 : $i]: ((k3_xboole_0 @ X21 @ X21) = (X21))),
% 34.81/35.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 34.81/35.03  thf('105', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('106', plain, (![X21 : $i]: ((k3_xboole_0 @ X21 @ X21) = (X21))),
% 34.81/35.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 34.81/35.03  thf('107', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('108', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['106', '107'])).
% 34.81/35.03  thf('109', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_C_3 @ sk_D_2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['105', '108'])).
% 34.81/35.03  thf('110', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('111', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('112', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ (k2_zfmisc_1 @ X1 @ X2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['110', '111'])).
% 34.81/35.03  thf('113', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('114', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2) @ (k2_zfmisc_1 @ X3 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['112', '113'])).
% 34.81/35.03  thf('115', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ X0) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_A @ sk_D_2)))),
% 34.81/35.03      inference('demod', [status(thm)], ['109', '114'])).
% 34.81/35.03  thf('116', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['15'])).
% 34.81/35.03  thf('117', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 34.81/35.03          (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['115', '116'])).
% 34.81/35.03  thf('118', plain,
% 34.81/35.03      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['104', '117'])).
% 34.81/35.03  thf('119', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('120', plain,
% 34.81/35.03      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03        (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['118', '119'])).
% 34.81/35.03  thf('121', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('122', plain,
% 34.81/35.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03         (k2_zfmisc_1 @ sk_A @ sk_D_2)) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('sup-', [status(thm)], ['120', '121'])).
% 34.81/35.03  thf('123', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('124', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['106', '107'])).
% 34.81/35.03  thf('125', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_A @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['123', '124'])).
% 34.81/35.03  thf('126', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('127', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B))
% 34.81/35.03         = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['122', '125', '126'])).
% 34.81/35.03  thf('128', plain,
% 34.81/35.03      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['103', '127'])).
% 34.81/35.03  thf('129', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('130', plain,
% 34.81/35.03      (![X32 : $i, X33 : $i]:
% 34.81/35.03         (((X32) = (k1_xboole_0))
% 34.81/35.03          | ((X33) = (k1_xboole_0))
% 34.81/35.03          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('131', plain,
% 34.81/35.03      ((((k2_zfmisc_1 @ sk_C_3 @ sk_D_2) != (k1_xboole_0))
% 34.81/35.03        | ((sk_A) = (k1_xboole_0))
% 34.81/35.03        | ((sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['129', '130'])).
% 34.81/35.03  thf('132', plain, (((sk_B) != (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('133', plain, (((sk_A) != (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('134', plain, (((k2_zfmisc_1 @ sk_C_3 @ sk_D_2) != (k1_xboole_0))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['131', '132', '133'])).
% 34.81/35.03  thf('135', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['128', '134'])).
% 34.81/35.03  thf('136', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('137', plain,
% 34.81/35.03      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X12 @ X13)
% 34.81/35.03          | (r2_hidden @ X12 @ X14)
% 34.81/35.03          | (r2_hidden @ X12 @ X15)
% 34.81/35.03          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 34.81/35.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 34.81/35.03  thf('138', plain,
% 34.81/35.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 34.81/35.03         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 34.81/35.03          | (r2_hidden @ X12 @ X14)
% 34.81/35.03          | ~ (r2_hidden @ X12 @ X13))),
% 34.81/35.03      inference('simplify', [status(thm)], ['137'])).
% 34.81/35.03  thf('139', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r1_tarski @ X0 @ X1)
% 34.81/35.03          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 34.81/35.03          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['136', '138'])).
% 34.81/35.03  thf('140', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 34.81/35.03      inference('clc', [status(thm)], ['22', '23'])).
% 34.81/35.03  thf('141', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 34.81/35.03          | (r1_tarski @ X1 @ X2)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['139', '140'])).
% 34.81/35.03  thf('142', plain,
% 34.81/35.03      (![X3 : $i, X5 : $i]:
% 34.81/35.03         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('143', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 34.81/35.03          | (r1_tarski @ X1 @ X0)
% 34.81/35.03          | (r1_tarski @ X1 @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['141', '142'])).
% 34.81/35.03  thf('144', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ X1 @ X0)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['143'])).
% 34.81/35.03  thf('145', plain,
% 34.81/35.03      (((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) | (r1_tarski @ sk_A @ sk_C_3))),
% 34.81/35.03      inference('sup+', [status(thm)], ['135', '144'])).
% 34.81/35.03  thf('146', plain,
% 34.81/35.03      (![X18 : $i, X19 : $i]: (((X18) != (X19)) | ~ (r2_xboole_0 @ X18 @ X19))),
% 34.81/35.03      inference('cnf', [status(esa)], [d8_xboole_0])).
% 34.81/35.03  thf('147', plain, (![X19 : $i]: ~ (r2_xboole_0 @ X19 @ X19)),
% 34.81/35.03      inference('simplify', [status(thm)], ['146'])).
% 34.81/35.03  thf('148', plain, ((r1_tarski @ sk_A @ sk_C_3)),
% 34.81/35.03      inference('clc', [status(thm)], ['145', '147'])).
% 34.81/35.03  thf('149', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('150', plain, (((k3_xboole_0 @ sk_A @ sk_C_3) = (sk_A))),
% 34.81/35.03      inference('sup-', [status(thm)], ['148', '149'])).
% 34.81/35.03  thf('151', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('152', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 34.81/35.03      inference('demod', [status(thm)], ['150', '151'])).
% 34.81/35.03  thf('153', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('demod', [status(thm)], ['36', '37'])).
% 34.81/35.03  thf('154', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['66'])).
% 34.81/35.03  thf('155', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['68', '69'])).
% 34.81/35.03  thf('156', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_A @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['123', '124'])).
% 34.81/35.03  thf('157', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D_2))
% 34.81/35.03         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['155', '156'])).
% 34.81/35.03  thf('158', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('159', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B))
% 34.81/35.03         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['157', '158'])).
% 34.81/35.03  thf('160', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('161', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['106', '107'])).
% 34.81/35.03  thf('162', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.81/35.03      inference('simplify', [status(thm)], ['15'])).
% 34.81/35.03  thf('163', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 34.81/35.03          (k2_zfmisc_1 @ X2 @ X0))),
% 34.81/35.03      inference('sup+', [status(thm)], ['161', '162'])).
% 34.81/35.03  thf('164', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 34.81/35.03          (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['160', '163'])).
% 34.81/35.03  thf('165', plain,
% 34.81/35.03      ((r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2) @ 
% 34.81/35.03        (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['159', '164'])).
% 34.81/35.03  thf('166', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 34.81/35.03      inference('demod', [status(thm)], ['150', '151'])).
% 34.81/35.03  thf('167', plain,
% 34.81/35.03      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_D_2) @ 
% 34.81/35.03        (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['165', '166'])).
% 34.81/35.03  thf('168', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('169', plain,
% 34.81/35.03      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_2) @ 
% 34.81/35.03         (k2_zfmisc_1 @ sk_C_3 @ sk_D_2)) = (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 34.81/35.03      inference('sup-', [status(thm)], ['167', '168'])).
% 34.81/35.03  thf('170', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2) @ (k2_zfmisc_1 @ X3 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['112', '113'])).
% 34.81/35.03  thf('171', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_A @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['123', '124'])).
% 34.81/35.03  thf('172', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('173', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 34.81/35.03          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 34.81/35.03      inference('sup-', [status(thm)], ['55', '56'])).
% 34.81/35.03  thf('174', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['66'])).
% 34.81/35.03  thf('175', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['106', '107'])).
% 34.81/35.03  thf('176', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03            (k2_zfmisc_1 @ X1 @ X0)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X1 @ sk_A) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['71', '76'])).
% 34.81/35.03  thf('177', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_C_3 @ (k3_xboole_0 @ sk_D_2 @ X0))
% 34.81/35.03            != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['175', '176'])).
% 34.81/35.03  thf('178', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_C_3 @ k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_D_2) @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['174', '177'])).
% 34.81/35.03  thf('179', plain,
% 34.81/35.03      (![X33 : $i]: ((k2_zfmisc_1 @ X33 @ k1_xboole_0) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['52'])).
% 34.81/35.03  thf('180', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('181', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D_2)) = (k1_xboole_0)))),
% 34.81/35.03      inference('demod', [status(thm)], ['178', '179', '180'])).
% 34.81/35.03  thf('182', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D_2)) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['181'])).
% 34.81/35.03  thf('183', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('demod', [status(thm)], ['36', '37'])).
% 34.81/35.03  thf('184', plain,
% 34.81/35.03      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2))
% 34.81/35.03        | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['182', '183'])).
% 34.81/35.03  thf('185', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ X0) @ sk_D_2)
% 34.81/35.03            != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['70', '77'])).
% 34.81/35.03  thf('186', plain,
% 34.81/35.03      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2) != (k1_xboole_0))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2))
% 34.81/35.03        | ((k3_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))
% 34.81/35.03        | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['184', '185'])).
% 34.81/35.03  thf('187', plain,
% 34.81/35.03      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['80'])).
% 34.81/35.03  thf('188', plain, (![X21 : $i]: ((k3_xboole_0 @ X21 @ X21) = (X21))),
% 34.81/35.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 34.81/35.03  thf('189', plain,
% 34.81/35.03      ((((k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2))
% 34.81/35.03        | ((sk_A) = (k1_xboole_0))
% 34.81/35.03        | ((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0)))),
% 34.81/35.03      inference('demod', [status(thm)], ['186', '187', '188'])).
% 34.81/35.03  thf('190', plain,
% 34.81/35.03      ((((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0))
% 34.81/35.03        | ((sk_A) = (k1_xboole_0))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['189'])).
% 34.81/35.03  thf('191', plain, (((sk_A) != (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('192', plain,
% 34.81/35.03      ((((k3_xboole_0 @ sk_D_2 @ sk_B) = (k1_xboole_0))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['190', '191'])).
% 34.81/35.03  thf('193', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('sup+', [status(thm)], ['93', '94'])).
% 34.81/35.03  thf('194', plain,
% 34.81/35.03      (((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_D_2) @ k1_xboole_0)
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['192', '193'])).
% 34.81/35.03  thf('195', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('196', plain,
% 34.81/35.03      (((r1_tarski @ (k3_xboole_0 @ sk_D_2 @ sk_B) @ k1_xboole_0)
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('demod', [status(thm)], ['194', '195'])).
% 34.81/35.03  thf('197', plain,
% 34.81/35.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X2 @ X3)
% 34.81/35.03          | (r2_hidden @ X2 @ X4)
% 34.81/35.03          | ~ (r1_tarski @ X3 @ X4))),
% 34.81/35.03      inference('cnf', [status(esa)], [d3_tarski])).
% 34.81/35.03  thf('198', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2))
% 34.81/35.03          | (r2_hidden @ X0 @ k1_xboole_0)
% 34.81/35.03          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['196', '197'])).
% 34.81/35.03  thf('199', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.81/35.03      inference('condensation', [status(thm)], ['5'])).
% 34.81/35.03  thf('200', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B))
% 34.81/35.03          | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('clc', [status(thm)], ['198', '199'])).
% 34.81/35.03  thf('201', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_2 @ sk_B)) = (k1_xboole_0))
% 34.81/35.03          | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['173', '200'])).
% 34.81/35.03  thf('202', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_2 @ sk_B))
% 34.81/35.03         = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['122', '125', '126'])).
% 34.81/35.03  thf('203', plain,
% 34.81/35.03      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))
% 34.81/35.03        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['201', '202'])).
% 34.81/35.03  thf('204', plain, (((k2_zfmisc_1 @ sk_C_3 @ sk_D_2) != (k1_xboole_0))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['131', '132', '133'])).
% 34.81/35.03  thf('205', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_D_2))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['203', '204'])).
% 34.81/35.03  thf('206', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ X1 @ X0)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['143'])).
% 34.81/35.03  thf('207', plain,
% 34.81/35.03      (((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) | (r1_tarski @ sk_B @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['205', '206'])).
% 34.81/35.03  thf('208', plain, (![X19 : $i]: ~ (r2_xboole_0 @ X19 @ X19)),
% 34.81/35.03      inference('simplify', [status(thm)], ['146'])).
% 34.81/35.03  thf('209', plain, ((r1_tarski @ sk_B @ sk_D_2)),
% 34.81/35.03      inference('clc', [status(thm)], ['207', '208'])).
% 34.81/35.03  thf('210', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('211', plain, (((k3_xboole_0 @ sk_B @ sk_D_2) = (sk_B))),
% 34.81/35.03      inference('sup-', [status(thm)], ['209', '210'])).
% 34.81/35.03  thf('212', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('213', plain, (((k3_xboole_0 @ sk_D_2 @ sk_B) = (sk_B))),
% 34.81/35.03      inference('demod', [status(thm)], ['211', '212'])).
% 34.81/35.03  thf('214', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_A @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['169', '170', '171', '172', '213'])).
% 34.81/35.03  thf('215', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('216', plain,
% 34.81/35.03      (((k2_zfmisc_1 @ sk_A @ sk_D_2) = (k2_zfmisc_1 @ sk_C_3 @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['214', '215'])).
% 34.81/35.03  thf('217', plain, (![X21 : $i]: ((k3_xboole_0 @ X21 @ X21) = (X21))),
% 34.81/35.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 34.81/35.03  thf('218', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ (k2_zfmisc_1 @ X1 @ X2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['110', '111'])).
% 34.81/35.03  thf('219', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['217', '218'])).
% 34.81/35.03  thf('220', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_D_2)
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D_2) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_C_3 @ sk_D_2)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['216', '219'])).
% 34.81/35.03  thf('221', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['217', '218'])).
% 34.81/35.03  thf('222', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_D_2)
% 34.81/35.03           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_3 @ X0) @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['220', '221'])).
% 34.81/35.03  thf('223', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ k1_xboole_0 @ sk_D_2)
% 34.81/35.03           = (k2_zfmisc_1 @ 
% 34.81/35.03              (k3_xboole_0 @ sk_C_3 @ (k4_xboole_0 @ X0 @ sk_A)) @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['154', '222'])).
% 34.81/35.03  thf('224', plain,
% 34.81/35.03      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['80'])).
% 34.81/35.03  thf('225', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k1_xboole_0)
% 34.81/35.03           = (k2_zfmisc_1 @ 
% 34.81/35.03              (k3_xboole_0 @ sk_C_3 @ (k4_xboole_0 @ X0 @ sk_A)) @ sk_D_2))),
% 34.81/35.03      inference('demod', [status(thm)], ['223', '224'])).
% 34.81/35.03  thf('226', plain,
% 34.81/35.03      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_3 @ sk_A) @ sk_D_2))),
% 34.81/35.03      inference('sup+', [status(thm)], ['153', '225'])).
% 34.81/35.03  thf('227', plain,
% 34.81/35.03      (![X32 : $i, X33 : $i]:
% 34.81/35.03         (((X32) = (k1_xboole_0))
% 34.81/35.03          | ((X33) = (k1_xboole_0))
% 34.81/35.03          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('228', plain,
% 34.81/35.03      ((((k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03        | ((k4_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0))
% 34.81/35.03        | ((sk_D_2) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['226', '227'])).
% 34.81/35.03  thf('229', plain,
% 34.81/35.03      ((((sk_D_2) = (k1_xboole_0))
% 34.81/35.03        | ((k4_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['228'])).
% 34.81/35.03  thf('230', plain, (((sk_B) != (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('231', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['66'])).
% 34.81/35.03  thf('232', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_3 @ sk_D_2) @ 
% 34.81/35.03              (k2_zfmisc_1 @ sk_A @ X0)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['123', '124'])).
% 34.81/35.03  thf('233', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('234', plain,
% 34.81/35.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X35 @ X37) @ (k3_xboole_0 @ X36 @ X38))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X35 @ X36) @ 
% 34.81/35.03              (k2_zfmisc_1 @ X37 @ X38)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 34.81/35.03  thf('235', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         ((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 34.81/35.03           = (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 34.81/35.03      inference('sup+', [status(thm)], ['233', '234'])).
% 34.81/35.03  thf('236', plain,
% 34.81/35.03      (![X32 : $i, X33 : $i]:
% 34.81/35.03         (((X32) = (k1_xboole_0))
% 34.81/35.03          | ((X33) = (k1_xboole_0))
% 34.81/35.03          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 34.81/35.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 34.81/35.03  thf('237', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 34.81/35.03            != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ X2) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['235', '236'])).
% 34.81/35.03  thf('238', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_D_2) = (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['232', '237'])).
% 34.81/35.03  thf('239', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_A))),
% 34.81/35.03      inference('demod', [status(thm)], ['150', '151'])).
% 34.81/35.03  thf('240', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_D_2) = (k1_xboole_0))
% 34.81/35.03          | ((sk_A) = (k1_xboole_0)))),
% 34.81/35.03      inference('demod', [status(thm)], ['238', '239'])).
% 34.81/35.03  thf('241', plain, (((sk_A) != (k1_xboole_0))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('242', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ X0 @ sk_D_2) = (k1_xboole_0)))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['240', '241'])).
% 34.81/35.03  thf('243', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_D_2) = (k1_xboole_0)))),
% 34.81/35.03      inference('sup-', [status(thm)], ['231', '242'])).
% 34.81/35.03  thf('244', plain,
% 34.81/35.03      (![X33 : $i]: ((k2_zfmisc_1 @ X33 @ k1_xboole_0) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['52'])).
% 34.81/35.03  thf('245', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 34.81/35.03  thf('246', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         (((k1_xboole_0) != (k1_xboole_0))
% 34.81/35.03          | ((k3_xboole_0 @ sk_D_2 @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0)))),
% 34.81/35.03      inference('demod', [status(thm)], ['243', '244', '245'])).
% 34.81/35.03  thf('247', plain,
% 34.81/35.03      (![X0 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ sk_D_2 @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify', [status(thm)], ['246'])).
% 34.81/35.03  thf('248', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.81/35.03           = (k4_xboole_0 @ X0 @ X1))),
% 34.81/35.03      inference('demod', [status(thm)], ['36', '37'])).
% 34.81/35.03  thf('249', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D_2 @ sk_B))),
% 34.81/35.03      inference('sup+', [status(thm)], ['247', '248'])).
% 34.81/35.03  thf('250', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ X1 @ X0)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['143'])).
% 34.81/35.03  thf('251', plain,
% 34.81/35.03      (((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) | (r1_tarski @ sk_D_2 @ sk_B))),
% 34.81/35.03      inference('sup+', [status(thm)], ['249', '250'])).
% 34.81/35.03  thf('252', plain, (![X19 : $i]: ~ (r2_xboole_0 @ X19 @ X19)),
% 34.81/35.03      inference('simplify', [status(thm)], ['146'])).
% 34.81/35.03  thf('253', plain, ((r1_tarski @ sk_D_2 @ sk_B)),
% 34.81/35.03      inference('clc', [status(thm)], ['251', '252'])).
% 34.81/35.03  thf('254', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('255', plain, (((k3_xboole_0 @ sk_D_2 @ sk_B) = (sk_D_2))),
% 34.81/35.03      inference('sup-', [status(thm)], ['253', '254'])).
% 34.81/35.03  thf('256', plain, (((k3_xboole_0 @ sk_D_2 @ sk_B) = (sk_B))),
% 34.81/35.03      inference('demod', [status(thm)], ['211', '212'])).
% 34.81/35.03  thf('257', plain, (((sk_D_2) = (sk_B))),
% 34.81/35.03      inference('sup+', [status(thm)], ['255', '256'])).
% 34.81/35.03  thf('258', plain, (((sk_D_2) != (k1_xboole_0))),
% 34.81/35.03      inference('demod', [status(thm)], ['230', '257'])).
% 34.81/35.03  thf('259', plain, (((k4_xboole_0 @ sk_C_3 @ sk_A) = (k1_xboole_0))),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['229', '258'])).
% 34.81/35.03  thf('260', plain,
% 34.81/35.03      (![X0 : $i, X1 : $i]:
% 34.81/35.03         ((r1_tarski @ X1 @ X0)
% 34.81/35.03          | (r2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['143'])).
% 34.81/35.03  thf('261', plain,
% 34.81/35.03      (((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) | (r1_tarski @ sk_C_3 @ sk_A))),
% 34.81/35.03      inference('sup+', [status(thm)], ['259', '260'])).
% 34.81/35.03  thf('262', plain, (![X19 : $i]: ~ (r2_xboole_0 @ X19 @ X19)),
% 34.81/35.03      inference('simplify', [status(thm)], ['146'])).
% 34.81/35.03  thf('263', plain, ((r1_tarski @ sk_C_3 @ sk_A)),
% 34.81/35.03      inference('clc', [status(thm)], ['261', '262'])).
% 34.81/35.03  thf('264', plain,
% 34.81/35.03      (![X24 : $i, X25 : $i]:
% 34.81/35.03         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 34.81/35.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 34.81/35.03  thf('265', plain, (((k3_xboole_0 @ sk_C_3 @ sk_A) = (sk_C_3))),
% 34.81/35.03      inference('sup-', [status(thm)], ['263', '264'])).
% 34.81/35.03  thf('266', plain, (((sk_A) = (sk_C_3))),
% 34.81/35.03      inference('sup+', [status(thm)], ['152', '265'])).
% 34.81/35.03  thf('267', plain, ((((sk_A) != (sk_C_3)) | ((sk_B) != (sk_D_2)))),
% 34.81/35.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.81/35.03  thf('268', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 34.81/35.03      inference('split', [status(esa)], ['267'])).
% 34.81/35.03  thf('269', plain, (((sk_D_2) = (sk_B))),
% 34.81/35.03      inference('sup+', [status(thm)], ['255', '256'])).
% 34.81/35.03  thf('270', plain, ((((sk_B) != (sk_D_2))) <= (~ (((sk_B) = (sk_D_2))))),
% 34.81/35.03      inference('split', [status(esa)], ['267'])).
% 34.81/35.03  thf('271', plain, ((((sk_D_2) != (sk_D_2))) <= (~ (((sk_B) = (sk_D_2))))),
% 34.81/35.03      inference('sup-', [status(thm)], ['269', '270'])).
% 34.81/35.03  thf('272', plain, ((((sk_B) = (sk_D_2)))),
% 34.81/35.03      inference('simplify', [status(thm)], ['271'])).
% 34.81/35.03  thf('273', plain, (~ (((sk_A) = (sk_C_3))) | ~ (((sk_B) = (sk_D_2)))),
% 34.81/35.03      inference('split', [status(esa)], ['267'])).
% 34.81/35.03  thf('274', plain, (~ (((sk_A) = (sk_C_3)))),
% 34.81/35.03      inference('sat_resolution*', [status(thm)], ['272', '273'])).
% 34.81/35.03  thf('275', plain, (((sk_A) != (sk_C_3))),
% 34.81/35.03      inference('simpl_trail', [status(thm)], ['268', '274'])).
% 34.81/35.03  thf('276', plain, ($false),
% 34.81/35.03      inference('simplify_reflect-', [status(thm)], ['266', '275'])).
% 34.81/35.03  
% 34.81/35.03  % SZS output end Refutation
% 34.81/35.03  
% 34.81/35.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
