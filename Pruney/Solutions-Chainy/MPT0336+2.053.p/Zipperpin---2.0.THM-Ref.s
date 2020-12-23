%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mqt2kFxaVc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:27 EST 2020

% Result     : Theorem 26.23s
% Output     : Refutation 26.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 195 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   24
%              Number of atoms          :  650 (1636 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
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
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53','56','57'])).

thf('59',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','63'])).

thf('65',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','64'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','69'])).

thf('71',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mqt2kFxaVc
% 0.15/0.37  % Computer   : n017.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 10:53:46 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 26.23/26.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.23/26.45  % Solved by: fo/fo7.sh
% 26.23/26.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.23/26.45  % done 11517 iterations in 25.956s
% 26.23/26.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.23/26.45  % SZS output start Refutation
% 26.23/26.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 26.23/26.45  thf(sk_B_type, type, sk_B: $i).
% 26.23/26.45  thf(sk_C_2_type, type, sk_C_2: $i).
% 26.23/26.45  thf(sk_A_type, type, sk_A: $i).
% 26.23/26.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.23/26.45  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 26.23/26.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 26.23/26.45  thf(sk_D_type, type, sk_D: $i).
% 26.23/26.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 26.23/26.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.23/26.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 26.23/26.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.23/26.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.23/26.45  thf(t149_zfmisc_1, conjecture,
% 26.23/26.45    (![A:$i,B:$i,C:$i,D:$i]:
% 26.23/26.45     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 26.23/26.45         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 26.23/26.45       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 26.23/26.45  thf(zf_stmt_0, negated_conjecture,
% 26.23/26.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 26.23/26.45        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 26.23/26.45            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 26.23/26.45          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 26.23/26.45    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 26.23/26.45  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 26.23/26.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.23/26.45  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 26.23/26.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.23/26.45  thf(d7_xboole_0, axiom,
% 26.23/26.45    (![A:$i,B:$i]:
% 26.23/26.45     ( ( r1_xboole_0 @ A @ B ) <=>
% 26.23/26.45       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 26.23/26.45  thf('2', plain,
% 26.23/26.45      (![X2 : $i, X3 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 26.23/26.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 26.23/26.45  thf('3', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['1', '2'])).
% 26.23/26.45  thf(commutativity_k3_xboole_0, axiom,
% 26.23/26.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 26.23/26.45  thf('4', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 26.23/26.45      inference('demod', [status(thm)], ['3', '4'])).
% 26.23/26.45  thf(t4_xboole_0, axiom,
% 26.23/26.45    (![A:$i,B:$i]:
% 26.23/26.45     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 26.23/26.45            ( r1_xboole_0 @ A @ B ) ) ) & 
% 26.23/26.45       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 26.23/26.45            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 26.23/26.45  thf('6', plain,
% 26.23/26.45      (![X9 : $i, X10 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X9 @ X10)
% 26.23/26.45          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t4_xboole_0])).
% 26.23/26.45  thf(l27_zfmisc_1, axiom,
% 26.23/26.45    (![A:$i,B:$i]:
% 26.23/26.45     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 26.23/26.45  thf('7', plain,
% 26.23/26.45      (![X27 : $i, X28 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 26.23/26.45      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 26.23/26.45  thf('8', plain,
% 26.23/26.45      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 26.23/26.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.23/26.45  thf('9', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('10', plain,
% 26.23/26.45      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 26.23/26.45      inference('demod', [status(thm)], ['8', '9'])).
% 26.23/26.45  thf(t28_xboole_1, axiom,
% 26.23/26.45    (![A:$i,B:$i]:
% 26.23/26.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 26.23/26.45  thf('11', plain,
% 26.23/26.45      (![X16 : $i, X17 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 26.23/26.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 26.23/26.45  thf('12', plain,
% 26.23/26.45      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 26.23/26.45         = (k3_xboole_0 @ sk_B @ sk_A))),
% 26.23/26.45      inference('sup-', [status(thm)], ['10', '11'])).
% 26.23/26.45  thf('13', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('14', plain,
% 26.23/26.45      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 26.23/26.45         = (k3_xboole_0 @ sk_B @ sk_A))),
% 26.23/26.45      inference('demod', [status(thm)], ['12', '13'])).
% 26.23/26.45  thf('15', plain,
% 26.23/26.45      (![X9 : $i, X11 : $i, X12 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 26.23/26.45          | ~ (r1_xboole_0 @ X9 @ X12))),
% 26.23/26.45      inference('cnf', [status(esa)], [t4_xboole_0])).
% 26.23/26.45  thf('16', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 26.23/26.45          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 26.23/26.45      inference('sup-', [status(thm)], ['14', '15'])).
% 26.23/26.45  thf('17', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 26.23/26.45          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 26.23/26.45      inference('sup-', [status(thm)], ['7', '16'])).
% 26.23/26.45  thf('18', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 26.23/26.45      inference('demod', [status(thm)], ['3', '4'])).
% 26.23/26.45  thf(t16_xboole_1, axiom,
% 26.23/26.45    (![A:$i,B:$i,C:$i]:
% 26.23/26.45     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 26.23/26.45       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 26.23/26.45  thf('20', plain,
% 26.23/26.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 26.23/26.45           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t16_xboole_1])).
% 26.23/26.45  thf('21', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 26.23/26.45           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 26.23/26.45      inference('sup+', [status(thm)], ['19', '20'])).
% 26.23/26.45  thf(t3_xboole_0, axiom,
% 26.23/26.45    (![A:$i,B:$i]:
% 26.23/26.45     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 26.23/26.45            ( r1_xboole_0 @ A @ B ) ) ) & 
% 26.23/26.45       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 26.23/26.45            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 26.23/26.45  thf('22', plain,
% 26.23/26.45      (![X5 : $i, X6 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 26.23/26.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.23/26.45  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 26.23/26.45      inference('demod', [status(thm)], ['3', '4'])).
% 26.23/26.45  thf('24', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('25', plain,
% 26.23/26.45      (![X9 : $i, X11 : $i, X12 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 26.23/26.45          | ~ (r1_xboole_0 @ X9 @ X12))),
% 26.23/26.45      inference('cnf', [status(esa)], [t4_xboole_0])).
% 26.23/26.45  thf('26', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 26.23/26.45          | ~ (r1_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('sup-', [status(thm)], ['24', '25'])).
% 26.23/26.45  thf('27', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 26.23/26.45      inference('sup-', [status(thm)], ['23', '26'])).
% 26.23/26.45  thf('28', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 26.23/26.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.23/26.45  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 26.23/26.45      inference('demod', [status(thm)], ['27', '28'])).
% 26.23/26.45  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 26.23/26.45      inference('sup-', [status(thm)], ['22', '29'])).
% 26.23/26.45  thf('31', plain,
% 26.23/26.45      (![X2 : $i, X3 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 26.23/26.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 26.23/26.45  thf('32', plain,
% 26.23/26.45      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['30', '31'])).
% 26.23/26.45  thf('33', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_2 @ X0)))),
% 26.23/26.45      inference('demod', [status(thm)], ['21', '32'])).
% 26.23/26.45  thf('34', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('35', plain,
% 26.23/26.45      (![X2 : $i, X4 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 26.23/26.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 26.23/26.45  thf('36', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('sup-', [status(thm)], ['34', '35'])).
% 26.23/26.45  thf('37', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         (((k1_xboole_0) != (k1_xboole_0))
% 26.23/26.45          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B))),
% 26.23/26.45      inference('sup-', [status(thm)], ['33', '36'])).
% 26.23/26.45  thf('38', plain,
% 26.23/26.45      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B)),
% 26.23/26.45      inference('simplify', [status(thm)], ['37'])).
% 26.23/26.45  thf('39', plain,
% 26.23/26.45      (![X2 : $i, X3 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 26.23/26.45      inference('cnf', [status(esa)], [d7_xboole_0])).
% 26.23/26.45  thf('40', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_B) = (k1_xboole_0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['38', '39'])).
% 26.23/26.45  thf('41', plain,
% 26.23/26.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 26.23/26.45           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t16_xboole_1])).
% 26.23/26.45  thf('42', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 26.23/26.45      inference('demod', [status(thm)], ['40', '41'])).
% 26.23/26.45  thf('43', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('44', plain,
% 26.23/26.45      (![X9 : $i, X10 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X9 @ X10)
% 26.23/26.45          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t4_xboole_0])).
% 26.23/26.45  thf('45', plain,
% 26.23/26.45      (![X9 : $i, X10 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X9 @ X10)
% 26.23/26.45          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t4_xboole_0])).
% 26.23/26.45  thf('46', plain,
% 26.23/26.45      (![X5 : $i, X7 : $i, X8 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X7 @ X5)
% 26.23/26.45          | ~ (r2_hidden @ X7 @ X8)
% 26.23/26.45          | ~ (r1_xboole_0 @ X5 @ X8))),
% 26.23/26.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.23/26.45  thf('47', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X1 @ X0)
% 26.23/26.45          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 26.23/26.45          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 26.23/26.45      inference('sup-', [status(thm)], ['45', '46'])).
% 26.23/26.45  thf('48', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]:
% 26.23/26.45         ((r1_xboole_0 @ X1 @ X0)
% 26.23/26.45          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 26.23/26.45          | (r1_xboole_0 @ X1 @ X0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['44', '47'])).
% 26.23/26.45  thf('49', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]:
% 26.23/26.45         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 26.23/26.45          | (r1_xboole_0 @ X1 @ X0))),
% 26.23/26.45      inference('simplify', [status(thm)], ['48'])).
% 26.23/26.45  thf('50', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]:
% 26.23/26.45         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 26.23/26.45          | (r1_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('sup-', [status(thm)], ['43', '49'])).
% 26.23/26.45  thf('51', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         (~ (r1_xboole_0 @ 
% 26.23/26.45             (k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_2) @ k1_xboole_0)
% 26.23/26.45          | (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 26.23/26.45      inference('sup-', [status(thm)], ['42', '50'])).
% 26.23/26.45  thf('52', plain,
% 26.23/26.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 26.23/26.45           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t16_xboole_1])).
% 26.23/26.45  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 26.23/26.45      inference('demod', [status(thm)], ['3', '4'])).
% 26.23/26.45  thf('54', plain,
% 26.23/26.45      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['30', '31'])).
% 26.23/26.45  thf('55', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 26.23/26.45  thf('56', plain,
% 26.23/26.45      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 26.23/26.45      inference('sup+', [status(thm)], ['54', '55'])).
% 26.23/26.45  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 26.23/26.45      inference('sup-', [status(thm)], ['22', '29'])).
% 26.23/26.45  thf('58', plain,
% 26.23/26.45      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B))),
% 26.23/26.45      inference('demod', [status(thm)], ['51', '52', '53', '56', '57'])).
% 26.23/26.45  thf('59', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 26.23/26.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.23/26.45  thf('60', plain,
% 26.23/26.45      (![X5 : $i, X7 : $i, X8 : $i]:
% 26.23/26.45         (~ (r2_hidden @ X7 @ X5)
% 26.23/26.45          | ~ (r2_hidden @ X7 @ X8)
% 26.23/26.45          | ~ (r1_xboole_0 @ X5 @ X8))),
% 26.23/26.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.23/26.45  thf('61', plain,
% 26.23/26.45      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['59', '60'])).
% 26.23/26.45  thf('62', plain,
% 26.23/26.45      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 26.23/26.45      inference('sup-', [status(thm)], ['58', '61'])).
% 26.23/26.45  thf('63', plain,
% 26.23/26.45      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['18', '62'])).
% 26.23/26.45  thf('64', plain,
% 26.23/26.45      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 26.23/26.45      inference('clc', [status(thm)], ['17', '63'])).
% 26.23/26.45  thf('65', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 26.23/26.45      inference('sup-', [status(thm)], ['6', '64'])).
% 26.23/26.45  thf(t78_xboole_1, axiom,
% 26.23/26.45    (![A:$i,B:$i,C:$i]:
% 26.23/26.45     ( ( r1_xboole_0 @ A @ B ) =>
% 26.23/26.45       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 26.23/26.45         ( k3_xboole_0 @ A @ C ) ) ))).
% 26.23/26.45  thf('66', plain,
% 26.23/26.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.23/26.45         (~ (r1_xboole_0 @ X18 @ X19)
% 26.23/26.45          | ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 26.23/26.45              = (k3_xboole_0 @ X18 @ X20)))),
% 26.23/26.45      inference('cnf', [status(esa)], [t78_xboole_1])).
% 26.23/26.45  thf('67', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 26.23/26.45           = (k3_xboole_0 @ sk_B @ X0))),
% 26.23/26.45      inference('sup-', [status(thm)], ['65', '66'])).
% 26.23/26.45  thf('68', plain,
% 26.23/26.45      (![X0 : $i, X1 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 26.23/26.45      inference('sup-', [status(thm)], ['34', '35'])).
% 26.23/26.45  thf('69', plain,
% 26.23/26.45      (![X0 : $i]:
% 26.23/26.45         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 26.23/26.45          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 26.23/26.45      inference('sup-', [status(thm)], ['67', '68'])).
% 26.23/26.45  thf('70', plain,
% 26.23/26.45      ((((k1_xboole_0) != (k1_xboole_0))
% 26.23/26.45        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B))),
% 26.23/26.45      inference('sup-', [status(thm)], ['5', '69'])).
% 26.23/26.45  thf('71', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 26.23/26.45      inference('simplify', [status(thm)], ['70'])).
% 26.23/26.45  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 26.23/26.45  
% 26.23/26.45  % SZS output end Refutation
% 26.23/26.45  
% 26.23/26.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
