%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o4J40q2PH6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:33 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  158 (1675 expanded)
%              Number of leaves         :   25 ( 522 expanded)
%              Depth                    :   23
%              Number of atoms          : 1124 (16639 expanded)
%              Number of equality atoms :  201 (2991 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('32',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X53: $i,X54: $i] :
      ( ( X54
        = ( k1_tarski @ X53 ) )
      | ( X54 = k1_xboole_0 )
      | ~ ( r1_tarski @ X54 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('62',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('65',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('70',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','63','71'])).

thf('73',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['60','72'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['58','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('78',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k5_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('88',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('92',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('101',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','104'])).

thf('106',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('108',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C_1 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('110',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['60','72'])).

thf('116',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('118',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['89','118'])).

thf('120',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','119'])).

thf('121',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','119'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = sk_B ) ),
    inference(demod,[status(thm)],['28','120','121'])).

thf('123',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['17','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('125',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('127',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','119'])).

thf('128',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['60','72'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o4J40q2PH6
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:14:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.48/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.67  % Solved by: fo/fo7.sh
% 0.48/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.67  % done 762 iterations in 0.210s
% 0.48/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.67  % SZS output start Refutation
% 0.48/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.67  thf(t43_zfmisc_1, conjecture,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.48/0.67          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.48/0.67          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.48/0.67          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.48/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.67        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.48/0.67             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.48/0.67             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.48/0.67             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.48/0.67    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.48/0.67  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(t95_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k3_xboole_0 @ A @ B ) =
% 0.48/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.48/0.67  thf('1', plain,
% 0.48/0.67      (![X23 : $i, X24 : $i]:
% 0.48/0.67         ((k3_xboole_0 @ X23 @ X24)
% 0.48/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.48/0.67              (k2_xboole_0 @ X23 @ X24)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.48/0.67  thf(t91_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.67  thf('2', plain,
% 0.48/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.48/0.67           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.67  thf('3', plain,
% 0.48/0.67      (![X23 : $i, X24 : $i]:
% 0.48/0.67         ((k3_xboole_0 @ X23 @ X24)
% 0.48/0.67           = (k5_xboole_0 @ X23 @ 
% 0.48/0.67              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.48/0.67      inference('demod', [status(thm)], ['1', '2'])).
% 0.48/0.67  thf('4', plain,
% 0.48/0.67      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.48/0.67         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.48/0.67      inference('sup+', [status(thm)], ['0', '3'])).
% 0.48/0.67  thf(t92_xboole_1, axiom,
% 0.48/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.67  thf('5', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.67  thf('6', plain,
% 0.48/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.48/0.67           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.67  thf('7', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.67  thf('8', plain,
% 0.48/0.67      (![X23 : $i, X24 : $i]:
% 0.48/0.67         ((k3_xboole_0 @ X23 @ X24)
% 0.48/0.67           = (k5_xboole_0 @ X23 @ 
% 0.48/0.67              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.48/0.67      inference('demod', [status(thm)], ['1', '2'])).
% 0.48/0.67  thf('9', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.67  thf('10', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.48/0.67           = (k3_xboole_0 @ X0 @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf(idempotence_k2_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.67  thf('11', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.67      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.48/0.67  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.67  thf('12', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.48/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.67  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.67      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.48/0.67  thf('14', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('demod', [status(thm)], ['7', '13'])).
% 0.48/0.67  thf('15', plain,
% 0.48/0.67      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.48/0.67         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['4', '14'])).
% 0.48/0.67  thf(t100_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.67  thf('16', plain,
% 0.48/0.67      (![X13 : $i, X14 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X13 @ X14)
% 0.48/0.67           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.67  thf('17', plain,
% 0.48/0.67      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.48/0.67         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.48/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.48/0.67  thf(t36_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.67  thf('18', plain,
% 0.48/0.67      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.48/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.67  thf(d3_tarski, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.67  thf('19', plain,
% 0.48/0.67      (![X1 : $i, X3 : $i]:
% 0.48/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.67  thf('20', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.67  thf(t1_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.48/0.67       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.48/0.67  thf('21', plain,
% 0.48/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X6 @ X7)
% 0.48/0.67          | ~ (r2_hidden @ X6 @ X8)
% 0.48/0.67          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.48/0.67  thf('22', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.48/0.67          | ~ (r2_hidden @ X1 @ X0)
% 0.48/0.67          | ~ (r2_hidden @ X1 @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.67  thf('23', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.48/0.67      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.67  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.48/0.67      inference('condensation', [status(thm)], ['23'])).
% 0.48/0.67  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.67      inference('sup-', [status(thm)], ['19', '24'])).
% 0.48/0.67  thf(d10_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.67  thf('26', plain,
% 0.48/0.67      (![X10 : $i, X12 : $i]:
% 0.48/0.67         (((X10) = (X12))
% 0.48/0.67          | ~ (r1_tarski @ X12 @ X10)
% 0.48/0.67          | ~ (r1_tarski @ X10 @ X12))),
% 0.48/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.67  thf('27', plain,
% 0.48/0.67      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.67  thf('28', plain,
% 0.48/0.67      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['18', '27'])).
% 0.48/0.67  thf('29', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(t7_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.67  thf('30', plain,
% 0.48/0.67      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.48/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.48/0.67  thf('31', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.67  thf(l3_zfmisc_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.48/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.48/0.67  thf('32', plain,
% 0.48/0.67      (![X53 : $i, X54 : $i]:
% 0.48/0.67         (((X54) = (k1_tarski @ X53))
% 0.48/0.67          | ((X54) = (k1_xboole_0))
% 0.48/0.67          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 0.48/0.67      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.48/0.67  thf('33', plain,
% 0.48/0.67      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.67  thf('34', plain,
% 0.48/0.67      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.67  thf('35', plain,
% 0.48/0.67      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.48/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.67  thf('36', plain,
% 0.48/0.67      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.67  thf('37', plain,
% 0.48/0.67      (![X53 : $i, X54 : $i]:
% 0.48/0.67         (((X54) = (k1_tarski @ X53))
% 0.48/0.67          | ((X54) = (k1_xboole_0))
% 0.48/0.67          | ~ (r1_tarski @ X54 @ (k1_tarski @ X53)))),
% 0.48/0.67      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.48/0.67  thf('38', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (r1_tarski @ X0 @ sk_B)
% 0.48/0.67          | ((sk_B) = (k1_xboole_0))
% 0.48/0.67          | ((X0) = (k1_xboole_0))
% 0.48/0.67          | ((X0) = (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.67  thf('39', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (((k4_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A))
% 0.48/0.67          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.48/0.67          | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['35', '38'])).
% 0.48/0.67  thf('40', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.48/0.67          | ((sk_B) = (k1_xboole_0))
% 0.48/0.67          | ((sk_B) = (k1_xboole_0))
% 0.48/0.67          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['34', '39'])).
% 0.48/0.67  thf('41', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.48/0.67          | ((sk_B) = (k1_xboole_0))
% 0.48/0.67          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.48/0.67      inference('simplify', [status(thm)], ['40'])).
% 0.48/0.67  thf('42', plain,
% 0.48/0.67      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.48/0.67         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.48/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.48/0.67  thf('43', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('demod', [status(thm)], ['7', '13'])).
% 0.48/0.67  thf('44', plain,
% 0.48/0.67      (((k1_tarski @ sk_A)
% 0.48/0.67         = (k5_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['42', '43'])).
% 0.48/0.67  thf('45', plain,
% 0.48/0.67      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))
% 0.48/0.67        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))
% 0.48/0.67        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['41', '44'])).
% 0.48/0.67  thf('46', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.48/0.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.67  thf('47', plain,
% 0.48/0.67      (![X13 : $i, X14 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X13 @ X14)
% 0.48/0.67           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.67  thf('48', plain,
% 0.48/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.48/0.67  thf('49', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.67  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['48', '49'])).
% 0.48/0.67  thf('51', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.67      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.48/0.67  thf('52', plain,
% 0.48/0.67      (![X23 : $i, X24 : $i]:
% 0.48/0.67         ((k3_xboole_0 @ X23 @ X24)
% 0.48/0.67           = (k5_xboole_0 @ X23 @ 
% 0.48/0.67              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.48/0.67      inference('demod', [status(thm)], ['1', '2'])).
% 0.48/0.67  thf('53', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ X0 @ X0)
% 0.48/0.68           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.68  thf('54', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.48/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.68  thf('55', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.48/0.68  thf('56', plain,
% 0.48/0.68      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.48/0.68  thf('57', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['50', '56'])).
% 0.48/0.68  thf('58', plain,
% 0.48/0.68      ((((k1_tarski @ sk_A) = (sk_C_1))
% 0.48/0.68        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['45', '57'])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('60', plain,
% 0.48/0.68      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.48/0.68         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('split', [status(esa)], ['59'])).
% 0.48/0.68  thf('61', plain,
% 0.48/0.68      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('split', [status(esa)], ['59'])).
% 0.48/0.68  thf('62', plain,
% 0.48/0.68      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('63', plain,
% 0.48/0.68      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['62'])).
% 0.48/0.68  thf('64', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('65', plain,
% 0.48/0.68      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('66', plain,
% 0.48/0.68      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('split', [status(esa)], ['65'])).
% 0.48/0.68  thf('67', plain,
% 0.48/0.68      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['64', '66'])).
% 0.48/0.68  thf('68', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.68  thf('69', plain,
% 0.48/0.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.48/0.68      inference('split', [status(esa)], ['59'])).
% 0.48/0.68  thf('70', plain,
% 0.48/0.68      ((((sk_B) != (sk_B)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.48/0.68  thf('71', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['70'])).
% 0.48/0.68  thf('72', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['61', '63', '71'])).
% 0.48/0.68  thf('73', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['60', '72'])).
% 0.48/0.68  thf('74', plain,
% 0.48/0.68      ((((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['58', '73'])).
% 0.48/0.68  thf('75', plain,
% 0.48/0.68      (((k1_tarski @ sk_A)
% 0.48/0.68         = (k5_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['42', '43'])).
% 0.48/0.68  thf('76', plain,
% 0.48/0.68      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_1 @ sk_B))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['74', '75'])).
% 0.48/0.68  thf('77', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '13'])).
% 0.48/0.68  thf('78', plain,
% 0.48/0.68      ((((sk_B) = (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['76', '77'])).
% 0.48/0.68  thf('79', plain,
% 0.48/0.68      ((((sk_B) = (k5_xboole_0 @ sk_C_1 @ sk_B))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['33', '78'])).
% 0.48/0.68  thf('80', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k5_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['79'])).
% 0.48/0.68  thf('81', plain,
% 0.48/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.48/0.68           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.68  thf('82', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.68  thf('83', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.48/0.68           = (k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['81', '82'])).
% 0.48/0.68  thf('84', plain,
% 0.48/0.68      ((((k5_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_B @ sk_B)) = (k1_xboole_0))
% 0.48/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['80', '83'])).
% 0.48/0.68  thf('85', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.48/0.68  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.48/0.68  thf('87', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['50', '56'])).
% 0.48/0.68  thf('88', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.48/0.68  thf('89', plain,
% 0.48/0.68      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.48/0.68      inference('split', [status(esa)], ['65'])).
% 0.48/0.68  thf('90', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('91', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ X23 @ X24)
% 0.48/0.68           = (k5_xboole_0 @ X23 @ 
% 0.48/0.68              (k5_xboole_0 @ X24 @ (k2_xboole_0 @ X23 @ X24))))),
% 0.48/0.68      inference('demod', [status(thm)], ['1', '2'])).
% 0.48/0.68  thf('92', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.68  thf('93', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.48/0.68  thf('94', plain,
% 0.48/0.68      ((![X0 : $i]: ((k5_xboole_0 @ sk_B @ X0) = (X0)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['92', '93'])).
% 0.48/0.68  thf('95', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          ((k3_xboole_0 @ sk_B @ X0)
% 0.48/0.68            = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0))))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['91', '94'])).
% 0.48/0.68  thf('96', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.68  thf('97', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X13 @ X14)
% 0.48/0.68           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.68  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.48/0.68  thf('99', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['97', '98'])).
% 0.48/0.68  thf('100', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['18', '27'])).
% 0.48/0.68  thf('101', plain,
% 0.48/0.68      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.48/0.68  thf('102', plain,
% 0.48/0.68      ((![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ X0)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['96', '101'])).
% 0.48/0.68  thf('103', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.68  thf('104', plain,
% 0.48/0.68      ((![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ X0)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['102', '103'])).
% 0.48/0.68  thf('105', plain,
% 0.48/0.68      ((![X0 : $i]: ((sk_B) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0))))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['95', '104'])).
% 0.48/0.68  thf('106', plain,
% 0.48/0.68      ((((sk_B) = (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['90', '105'])).
% 0.48/0.68  thf('107', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '13'])).
% 0.48/0.68  thf('108', plain,
% 0.48/0.68      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_1 @ sk_B)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['106', '107'])).
% 0.48/0.68  thf('109', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.48/0.68  thf('110', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.48/0.68  thf('111', plain,
% 0.48/0.68      ((![X0 : $i]: ((sk_B) = (k4_xboole_0 @ X0 @ X0)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['109', '110'])).
% 0.48/0.68  thf('112', plain,
% 0.48/0.68      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.48/0.68  thf('113', plain,
% 0.48/0.68      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.48/0.68         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['111', '112'])).
% 0.48/0.68  thf('114', plain,
% 0.48/0.68      ((((k1_tarski @ sk_A) = (sk_C_1))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.48/0.68      inference('demod', [status(thm)], ['108', '113'])).
% 0.48/0.68  thf('115', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['60', '72'])).
% 0.48/0.68  thf('116', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 0.48/0.68  thf('117', plain,
% 0.48/0.68      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['65'])).
% 0.48/0.68  thf('118', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.48/0.68      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 0.48/0.68  thf('119', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['89', '118'])).
% 0.48/0.68  thf('120', plain, (((sk_B) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['88', '119'])).
% 0.48/0.68  thf('121', plain, (((sk_B) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['88', '119'])).
% 0.48/0.68  thf('122', plain, (![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['28', '120', '121'])).
% 0.48/0.68  thf('123', plain, (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['17', '122'])).
% 0.48/0.68  thf('124', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['7', '13'])).
% 0.48/0.68  thf('125', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_1 @ sk_B))),
% 0.48/0.68      inference('sup+', [status(thm)], ['123', '124'])).
% 0.48/0.68  thf('126', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['50', '56'])).
% 0.48/0.68  thf('127', plain, (((sk_B) = (k1_xboole_0))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['88', '119'])).
% 0.48/0.68  thf('128', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['126', '127'])).
% 0.48/0.68  thf('129', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.48/0.68      inference('demod', [status(thm)], ['125', '128'])).
% 0.48/0.68  thf('130', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.48/0.68      inference('simpl_trail', [status(thm)], ['60', '72'])).
% 0.48/0.68  thf('131', plain, ($false),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
