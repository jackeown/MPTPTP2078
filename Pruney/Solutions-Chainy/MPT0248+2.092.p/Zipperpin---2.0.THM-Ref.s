%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CmazaSghK1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:31 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  271 (19011 expanded)
%              Number of leaves         :   31 (6154 expanded)
%              Depth                    :   37
%              Number of atoms          : 1915 (162894 expanded)
%              Number of equality atoms :  237 (18195 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
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
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) ),
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
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( X32 = X29 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32 = X29 )
      | ~ ( r2_hidden @ X32 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X62: $i,X64: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X62 ) @ X64 )
      | ~ ( r2_hidden @ X62 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_tarski @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('62',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('67',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74','83','84'])).

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('93',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['90','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['85','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','97'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
      | ( ( k3_tarski @ sk_B )
        = sk_A ) ) ),
    inference('sup+',[status(thm)],['65','103'])).

thf('105',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( ( k3_tarski @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['18','104'])).

thf('106',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['106'])).

thf('109',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('113',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X62: $i,X64: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X62 ) @ X64 )
      | ~ ( r2_hidden @ X62 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('117',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('119',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['120'])).

thf('122',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,
    ( ( k1_xboole_0 = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['106'])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['108','110','126'])).

thf('128',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['107','127'])).

thf('129',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('130',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['17','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_tarski @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = sk_B )
      | ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('137',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['135','137'])).

thf('139',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('143',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C_2 ) )
      | ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','102'])).

thf('146',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = sk_C_2 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['107','127'])).

thf('148',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('149',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['90','98'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['130','150','153'])).

thf('155',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('156',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('157',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r2_hidden @ X62 @ X63 )
      | ~ ( r1_tarski @ ( k1_tarski @ X62 ) @ X63 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['155','158'])).

thf('160',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('163',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['161','165'])).

thf('167',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('170',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('171',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r2_hidden @ ( k3_tarski @ sk_B ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['154','172'])).

thf('174',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('175',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B ) @ sk_C_2 )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('179',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','128'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('183',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_C_2 = sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('185',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('186',plain,(
    sk_C_2 != sk_B ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['183','186'])).

thf('188',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('189',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('190',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('191',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('193',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('196',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('198',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['196','199'])).

thf('201',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['130','150','153'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['205','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','209'])).

thf('211',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('212',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['187','213'])).

thf('215',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['214','217'])).

thf('219',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('222',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['120'])).

thf('224',plain,
    ( ( k1_xboole_0 = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('225',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74','83','84'])).

thf('228',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('230',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','97'])).

thf('232',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['107','127'])).

thf('234',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['120'])).

thf('236',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['234','235'])).

thf('237',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['223','236'])).

thf('238',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['222','237'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CmazaSghK1
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.73/1.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.73/1.94  % Solved by: fo/fo7.sh
% 1.73/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.94  % done 3598 iterations in 1.487s
% 1.73/1.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.73/1.94  % SZS output start Refutation
% 1.73/1.94  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.73/1.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.73/1.94  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.73/1.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.73/1.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.73/1.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.73/1.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.73/1.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.73/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.73/1.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.73/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.73/1.94  thf(t43_zfmisc_1, conjecture,
% 1.73/1.94    (![A:$i,B:$i,C:$i]:
% 1.73/1.94     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.73/1.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.73/1.94          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.73/1.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.73/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.94    (~( ![A:$i,B:$i,C:$i]:
% 1.73/1.94        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.73/1.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.73/1.94             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.73/1.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.73/1.94    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.73/1.94  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.94  thf(t95_xboole_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( k3_xboole_0 @ A @ B ) =
% 1.73/1.94       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.73/1.94  thf('1', plain,
% 1.73/1.94      (![X27 : $i, X28 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.94           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 1.73/1.94              (k2_xboole_0 @ X27 @ X28)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.73/1.94  thf(t91_xboole_1, axiom,
% 1.73/1.94    (![A:$i,B:$i,C:$i]:
% 1.73/1.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.73/1.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.73/1.94  thf('2', plain,
% 1.73/1.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.73/1.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.73/1.94  thf('3', plain,
% 1.73/1.94      (![X27 : $i, X28 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.94           = (k5_xboole_0 @ X27 @ 
% 1.73/1.94              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.94  thf('4', plain,
% 1.73/1.94      (((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.73/1.94         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 1.73/1.94      inference('sup+', [status(thm)], ['0', '3'])).
% 1.73/1.94  thf(t92_xboole_1, axiom,
% 1.73/1.94    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.73/1.94  thf('5', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 1.73/1.94      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.73/1.94  thf('6', plain,
% 1.73/1.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.73/1.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.73/1.94  thf('7', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.73/1.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.94      inference('sup+', [status(thm)], ['5', '6'])).
% 1.73/1.94  thf('8', plain,
% 1.73/1.94      (![X27 : $i, X28 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.94           = (k5_xboole_0 @ X27 @ 
% 1.73/1.94              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.94  thf('9', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.73/1.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.94      inference('sup+', [status(thm)], ['5', '6'])).
% 1.73/1.94  thf('10', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 1.73/1.94           = (k3_xboole_0 @ X0 @ X0))),
% 1.73/1.94      inference('sup+', [status(thm)], ['8', '9'])).
% 1.73/1.94  thf(idempotence_k2_xboole_0, axiom,
% 1.73/1.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.73/1.94  thf('11', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 1.73/1.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.73/1.94  thf(idempotence_k3_xboole_0, axiom,
% 1.73/1.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.73/1.94  thf('12', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 1.73/1.94      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.73/1.94  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.73/1.94      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.73/1.94  thf('14', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.94      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.94  thf('15', plain,
% 1.73/1.94      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 1.73/1.94         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_2)))),
% 1.73/1.94      inference('sup+', [status(thm)], ['4', '14'])).
% 1.73/1.94  thf(t100_xboole_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.73/1.94  thf('16', plain,
% 1.73/1.94      (![X13 : $i, X14 : $i]:
% 1.73/1.94         ((k4_xboole_0 @ X13 @ X14)
% 1.73/1.94           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.94  thf('17', plain,
% 1.73/1.94      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 1.73/1.94         = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.94      inference('demod', [status(thm)], ['15', '16'])).
% 1.73/1.94  thf('18', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.94  thf(d3_tarski, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( r1_tarski @ A @ B ) <=>
% 1.73/1.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.73/1.94  thf('19', plain,
% 1.73/1.94      (![X1 : $i, X3 : $i]:
% 1.73/1.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.94      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.94  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.94  thf(t7_xboole_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.73/1.94  thf('21', plain,
% 1.73/1.94      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 1.73/1.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.73/1.94  thf('22', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 1.73/1.94      inference('sup+', [status(thm)], ['20', '21'])).
% 1.73/1.94  thf('23', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.94          | (r2_hidden @ X0 @ X2)
% 1.73/1.94          | ~ (r1_tarski @ X1 @ X2))),
% 1.73/1.94      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.94  thf('24', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.73/1.94      inference('sup-', [status(thm)], ['22', '23'])).
% 1.73/1.94  thf('25', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         ((r1_tarski @ sk_B @ X0)
% 1.73/1.94          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tarski @ sk_A)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['19', '24'])).
% 1.73/1.94  thf(d1_tarski, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.73/1.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.73/1.94  thf('26', plain,
% 1.73/1.94      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X32 @ X31)
% 1.73/1.94          | ((X32) = (X29))
% 1.73/1.94          | ((X31) != (k1_tarski @ X29)))),
% 1.73/1.94      inference('cnf', [status(esa)], [d1_tarski])).
% 1.73/1.94  thf('27', plain,
% 1.73/1.94      (![X29 : $i, X32 : $i]:
% 1.73/1.94         (((X32) = (X29)) | ~ (r2_hidden @ X32 @ (k1_tarski @ X29)))),
% 1.73/1.94      inference('simplify', [status(thm)], ['26'])).
% 1.73/1.94  thf('28', plain,
% 1.73/1.94      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_C @ X0 @ sk_B) = (sk_A)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['25', '27'])).
% 1.73/1.94  thf('29', plain,
% 1.73/1.94      (![X1 : $i, X3 : $i]:
% 1.73/1.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.94      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.94  thf('30', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         ((r2_hidden @ sk_A @ sk_B)
% 1.73/1.94          | (r1_tarski @ sk_B @ X0)
% 1.73/1.94          | (r1_tarski @ sk_B @ X0))),
% 1.73/1.94      inference('sup+', [status(thm)], ['28', '29'])).
% 1.73/1.94  thf('31', plain,
% 1.73/1.94      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r2_hidden @ sk_A @ sk_B))),
% 1.73/1.94      inference('simplify', [status(thm)], ['30'])).
% 1.73/1.94  thf(l1_zfmisc_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.73/1.94  thf('32', plain,
% 1.73/1.94      (![X62 : $i, X64 : $i]:
% 1.73/1.94         ((r1_tarski @ (k1_tarski @ X62) @ X64) | ~ (r2_hidden @ X62 @ X64))),
% 1.73/1.94      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.73/1.94  thf('33', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         ((r1_tarski @ sk_B @ X0) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.73/1.94      inference('sup-', [status(thm)], ['31', '32'])).
% 1.73/1.94  thf('34', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 1.73/1.94      inference('sup+', [status(thm)], ['20', '21'])).
% 1.73/1.94  thf(d10_xboole_0, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.73/1.94  thf('35', plain,
% 1.73/1.94      (![X10 : $i, X12 : $i]:
% 1.73/1.94         (((X10) = (X12))
% 1.73/1.94          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.94          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.94  thf('36', plain,
% 1.73/1.94      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 1.73/1.94        | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['34', '35'])).
% 1.73/1.94  thf('37', plain,
% 1.73/1.94      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['33', '36'])).
% 1.73/1.94  thf(t69_enumset1, axiom,
% 1.73/1.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.73/1.94  thf('38', plain,
% 1.73/1.94      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 1.73/1.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.94  thf(l51_zfmisc_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]:
% 1.73/1.94     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.73/1.94  thf('39', plain,
% 1.73/1.94      (![X65 : $i, X66 : $i]:
% 1.73/1.94         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.73/1.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.73/1.94  thf('40', plain,
% 1.73/1.94      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.73/1.94      inference('sup+', [status(thm)], ['38', '39'])).
% 1.73/1.94  thf('41', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 1.73/1.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.73/1.94  thf('42', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.73/1.94      inference('demod', [status(thm)], ['40', '41'])).
% 1.73/1.94  thf('43', plain,
% 1.73/1.94      (![X0 : $i]: (((k3_tarski @ sk_B) = (sk_A)) | (r1_tarski @ sk_B @ X0))),
% 1.73/1.94      inference('sup+', [status(thm)], ['37', '42'])).
% 1.73/1.94  thf('44', plain,
% 1.73/1.94      (![X1 : $i, X3 : $i]:
% 1.73/1.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.94      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.94  thf('45', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 1.73/1.94      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.73/1.94  thf('46', plain,
% 1.73/1.94      (![X13 : $i, X14 : $i]:
% 1.73/1.94         ((k4_xboole_0 @ X13 @ X14)
% 1.73/1.94           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.94  thf(t1_xboole_0, axiom,
% 1.73/1.94    (![A:$i,B:$i,C:$i]:
% 1.73/1.94     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.73/1.94       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.73/1.94  thf('47', plain,
% 1.73/1.94      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X6 @ X7)
% 1.73/1.94          | ~ (r2_hidden @ X6 @ X8)
% 1.73/1.94          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.73/1.94  thf('48', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.73/1.94          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.94          | ~ (r2_hidden @ X2 @ X1))),
% 1.73/1.94      inference('sup-', [status(thm)], ['46', '47'])).
% 1.73/1.94  thf(t36_xboole_1, axiom,
% 1.73/1.94    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.73/1.94  thf('49', plain,
% 1.73/1.94      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.73/1.94      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.94  thf('50', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.94          | (r2_hidden @ X0 @ X2)
% 1.73/1.94          | ~ (r1_tarski @ X1 @ X2))),
% 1.73/1.94      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.94  thf('51', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['49', '50'])).
% 1.73/1.94  thf('52', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.94          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.73/1.94      inference('clc', [status(thm)], ['48', '51'])).
% 1.73/1.94  thf('53', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         (~ (r2_hidden @ X1 @ X0)
% 1.73/1.94          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['45', '52'])).
% 1.73/1.94  thf('54', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['49', '50'])).
% 1.73/1.94  thf('55', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.73/1.94      inference('clc', [status(thm)], ['53', '54'])).
% 1.73/1.94  thf('56', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 1.73/1.94      inference('sup-', [status(thm)], ['44', '55'])).
% 1.73/1.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.73/1.94  thf('57', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 1.73/1.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.73/1.94  thf('58', plain,
% 1.73/1.94      (![X10 : $i, X12 : $i]:
% 1.73/1.94         (((X10) = (X12))
% 1.73/1.94          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.94          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.94  thf('59', plain,
% 1.73/1.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['57', '58'])).
% 1.73/1.94  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.73/1.94      inference('sup-', [status(thm)], ['56', '59'])).
% 1.73/1.94  thf('61', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 1.73/1.94      inference('sup-', [status(thm)], ['44', '55'])).
% 1.73/1.94  thf('62', plain,
% 1.73/1.94      (![X10 : $i, X12 : $i]:
% 1.73/1.94         (((X10) = (X12))
% 1.73/1.94          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.94          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.94  thf('63', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 1.73/1.94          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['61', '62'])).
% 1.73/1.94  thf('64', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['60', '63'])).
% 1.73/1.94  thf('65', plain,
% 1.73/1.94      (![X0 : $i]:
% 1.73/1.94         (((k3_tarski @ sk_B) = (sk_A)) | ((sk_B) = (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.94      inference('sup-', [status(thm)], ['43', '64'])).
% 1.73/1.94  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.73/1.94      inference('sup-', [status(thm)], ['56', '59'])).
% 1.73/1.94  thf('67', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 1.73/1.94      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.73/1.94  thf('68', plain,
% 1.73/1.94      (![X27 : $i, X28 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.94           = (k5_xboole_0 @ X27 @ 
% 1.73/1.94              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.94      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.94  thf('69', plain,
% 1.73/1.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.73/1.94         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.73/1.94           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.73/1.94  thf('70', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 1.73/1.94           = (k5_xboole_0 @ X2 @ 
% 1.73/1.94              (k5_xboole_0 @ X1 @ 
% 1.73/1.94               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))))),
% 1.73/1.94      inference('sup+', [status(thm)], ['68', '69'])).
% 1.73/1.94  thf('71', plain,
% 1.73/1.94      (![X0 : $i, X1 : $i]:
% 1.73/1.94         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 1.73/1.94           = (k5_xboole_0 @ X1 @ 
% 1.73/1.94              (k5_xboole_0 @ X1 @ 
% 1.73/1.94               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))))),
% 1.73/1.94      inference('sup+', [status(thm)], ['67', '70'])).
% 1.73/1.94  thf('72', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 1.73/1.94      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.73/1.94  thf('73', plain,
% 1.73/1.94      (![X13 : $i, X14 : $i]:
% 1.73/1.94         ((k4_xboole_0 @ X13 @ X14)
% 1.73/1.94           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.73/1.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.95  thf('74', plain,
% 1.73/1.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['72', '73'])).
% 1.73/1.95  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['56', '59'])).
% 1.73/1.95  thf('76', plain,
% 1.73/1.95      (![X13 : $i, X14 : $i]:
% 1.73/1.95         ((k4_xboole_0 @ X13 @ X14)
% 1.73/1.95           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.73/1.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.95  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.73/1.95      inference('demod', [status(thm)], ['10', '11', '12'])).
% 1.73/1.95  thf('78', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['76', '77'])).
% 1.73/1.95  thf('79', plain,
% 1.73/1.95      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.73/1.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.95  thf('80', plain,
% 1.73/1.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['57', '58'])).
% 1.73/1.95  thf('81', plain,
% 1.73/1.95      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['79', '80'])).
% 1.73/1.95  thf('82', plain,
% 1.73/1.95      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.73/1.95      inference('demod', [status(thm)], ['78', '81'])).
% 1.73/1.95  thf('83', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 1.73/1.95      inference('sup+', [status(thm)], ['75', '82'])).
% 1.73/1.95  thf('84', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('85', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['71', '74', '83', '84'])).
% 1.73/1.95  thf('86', plain,
% 1.73/1.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.73/1.95           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.73/1.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.73/1.95  thf('87', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 1.73/1.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.73/1.95  thf('88', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.73/1.95           = (k1_xboole_0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['86', '87'])).
% 1.73/1.95  thf('89', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('90', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.73/1.95           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['88', '89'])).
% 1.73/1.95  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['56', '59'])).
% 1.73/1.95  thf('92', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 1.73/1.95      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.73/1.95  thf('93', plain,
% 1.73/1.95      (![X27 : $i, X28 : $i]:
% 1.73/1.95         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.95           = (k5_xboole_0 @ X27 @ 
% 1.73/1.95              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.95      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.95  thf('94', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((k3_xboole_0 @ X0 @ X0)
% 1.73/1.95           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['92', '93'])).
% 1.73/1.95  thf('95', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 1.73/1.95      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.73/1.95  thf('96', plain,
% 1.73/1.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['72', '73'])).
% 1.73/1.95  thf('97', plain,
% 1.73/1.95      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.73/1.95  thf('98', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['91', '97'])).
% 1.73/1.95  thf('99', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.73/1.95      inference('demod', [status(thm)], ['90', '98'])).
% 1.73/1.95  thf('100', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) = (X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['85', '99'])).
% 1.73/1.95  thf('101', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['91', '97'])).
% 1.73/1.95  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.73/1.95      inference('demod', [status(thm)], ['100', '101'])).
% 1.73/1.95  thf('103', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 1.73/1.95      inference('sup+', [status(thm)], ['66', '102'])).
% 1.73/1.95  thf('104', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (((k2_xboole_0 @ sk_B @ X0) = (X0)) | ((k3_tarski @ sk_B) = (sk_A)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['65', '103'])).
% 1.73/1.95  thf('105', plain,
% 1.73/1.95      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((k3_tarski @ sk_B) = (sk_A)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['18', '104'])).
% 1.73/1.95  thf('106', plain,
% 1.73/1.95      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.95  thf('107', plain,
% 1.73/1.95      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 1.73/1.95         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('split', [status(esa)], ['106'])).
% 1.73/1.95  thf('108', plain,
% 1.73/1.95      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.73/1.95      inference('split', [status(esa)], ['106'])).
% 1.73/1.95  thf('109', plain,
% 1.73/1.95      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.95  thf('110', plain,
% 1.73/1.95      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('split', [status(esa)], ['109'])).
% 1.73/1.95  thf('111', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 1.73/1.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.73/1.95  thf('112', plain,
% 1.73/1.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r2_hidden @ sk_A @ sk_B))),
% 1.73/1.95      inference('simplify', [status(thm)], ['30'])).
% 1.73/1.95  thf('113', plain,
% 1.73/1.95      (![X10 : $i, X12 : $i]:
% 1.73/1.95         (((X10) = (X12))
% 1.73/1.95          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.95          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.95  thf('114', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r2_hidden @ sk_A @ sk_B)
% 1.73/1.95          | ~ (r1_tarski @ X0 @ sk_B)
% 1.73/1.95          | ((X0) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['112', '113'])).
% 1.73/1.95  thf('115', plain, ((((k1_xboole_0) = (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.73/1.95      inference('sup-', [status(thm)], ['111', '114'])).
% 1.73/1.95  thf('116', plain,
% 1.73/1.95      (![X62 : $i, X64 : $i]:
% 1.73/1.95         ((r1_tarski @ (k1_tarski @ X62) @ X64) | ~ (r2_hidden @ X62 @ X64))),
% 1.73/1.95      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.73/1.95  thf('117', plain,
% 1.73/1.95      ((((k1_xboole_0) = (sk_B)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.73/1.95      inference('sup-', [status(thm)], ['115', '116'])).
% 1.73/1.95  thf('118', plain,
% 1.73/1.95      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 1.73/1.95        | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['34', '35'])).
% 1.73/1.95  thf('119', plain,
% 1.73/1.95      ((((k1_xboole_0) = (sk_B)) | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['117', '118'])).
% 1.73/1.95  thf('120', plain,
% 1.73/1.95      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 1.73/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.95  thf('121', plain,
% 1.73/1.95      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('split', [status(esa)], ['120'])).
% 1.73/1.95  thf('122', plain,
% 1.73/1.95      (((((sk_B) != (sk_B)) | ((k1_xboole_0) = (sk_B))))
% 1.73/1.95         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('sup-', [status(thm)], ['119', '121'])).
% 1.73/1.95  thf('123', plain,
% 1.73/1.95      ((((k1_xboole_0) = (sk_B))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('simplify', [status(thm)], ['122'])).
% 1.73/1.95  thf('124', plain,
% 1.73/1.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.73/1.95      inference('split', [status(esa)], ['106'])).
% 1.73/1.95  thf('125', plain,
% 1.73/1.95      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.73/1.95         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('sup-', [status(thm)], ['123', '124'])).
% 1.73/1.95  thf('126', plain,
% 1.73/1.95      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('simplify', [status(thm)], ['125'])).
% 1.73/1.95  thf('127', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('sat_resolution*', [status(thm)], ['108', '110', '126'])).
% 1.73/1.95  thf('128', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.73/1.95      inference('simpl_trail', [status(thm)], ['107', '127'])).
% 1.73/1.95  thf('129', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('130', plain,
% 1.73/1.95      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B)))
% 1.73/1.95         = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['17', '129'])).
% 1.73/1.95  thf('131', plain,
% 1.73/1.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['33', '36'])).
% 1.73/1.95  thf('132', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['60', '63'])).
% 1.73/1.95  thf('133', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (((k1_tarski @ sk_A) = (sk_B)) | ((sk_B) = (k4_xboole_0 @ X0 @ X0)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['131', '132'])).
% 1.73/1.95  thf('134', plain,
% 1.73/1.95      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 1.73/1.95        | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['34', '35'])).
% 1.73/1.95  thf('135', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r1_tarski @ sk_B @ sk_B)
% 1.73/1.95          | ((sk_B) = (k4_xboole_0 @ X0 @ X0))
% 1.73/1.95          | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['133', '134'])).
% 1.73/1.95  thf('136', plain,
% 1.73/1.95      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.73/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.95  thf('137', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.73/1.95      inference('simplify', [status(thm)], ['136'])).
% 1.73/1.95  thf('138', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (((sk_B) = (k4_xboole_0 @ X0 @ X0)) | ((k1_tarski @ sk_A) = (sk_B)))),
% 1.73/1.95      inference('demod', [status(thm)], ['135', '137'])).
% 1.73/1.95  thf('139', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('140', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (((sk_B) = (k4_xboole_0 @ X0 @ X0))
% 1.73/1.95          | ((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B)))),
% 1.73/1.95      inference('demod', [status(thm)], ['138', '139'])).
% 1.73/1.95  thf('141', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.95  thf('142', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('143', plain,
% 1.73/1.95      (((k1_tarski @ (k3_tarski @ sk_B)) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['141', '142'])).
% 1.73/1.95  thf('144', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (((k1_tarski @ (k3_tarski @ sk_B))
% 1.73/1.95            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C_2))
% 1.73/1.95          | ((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['140', '143'])).
% 1.73/1.95  thf('145', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 1.73/1.95      inference('sup+', [status(thm)], ['66', '102'])).
% 1.73/1.95  thf('146', plain,
% 1.73/1.95      ((((k1_tarski @ (k3_tarski @ sk_B)) = (sk_C_2))
% 1.73/1.95        | ((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B)))),
% 1.73/1.95      inference('demod', [status(thm)], ['144', '145'])).
% 1.73/1.95  thf('147', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.73/1.95      inference('simpl_trail', [status(thm)], ['107', '127'])).
% 1.73/1.95  thf('148', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('149', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B)))),
% 1.73/1.95      inference('demod', [status(thm)], ['147', '148'])).
% 1.73/1.95  thf('150', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['146', '149'])).
% 1.73/1.95  thf('151', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.73/1.95      inference('demod', [status(thm)], ['90', '98'])).
% 1.73/1.95  thf('152', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('153', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['151', '152'])).
% 1.73/1.95  thf('154', plain,
% 1.73/1.95      (((k5_xboole_0 @ sk_B @ sk_C_2) = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['130', '150', '153'])).
% 1.73/1.95  thf('155', plain,
% 1.73/1.95      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 1.73/1.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.95  thf('156', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.73/1.95      inference('simplify', [status(thm)], ['136'])).
% 1.73/1.95  thf('157', plain,
% 1.73/1.95      (![X62 : $i, X63 : $i]:
% 1.73/1.95         ((r2_hidden @ X62 @ X63) | ~ (r1_tarski @ (k1_tarski @ X62) @ X63))),
% 1.73/1.95      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.73/1.95  thf('158', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['156', '157'])).
% 1.73/1.95  thf('159', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['155', '158'])).
% 1.73/1.95  thf('160', plain,
% 1.73/1.95      (![X6 : $i, X7 : $i, X9 : $i]:
% 1.73/1.95         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 1.73/1.95          | (r2_hidden @ X6 @ X9)
% 1.73/1.95          | ~ (r2_hidden @ X6 @ X7))),
% 1.73/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.73/1.95  thf('161', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((r2_hidden @ X0 @ X1)
% 1.73/1.95          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['159', '160'])).
% 1.73/1.95  thf('162', plain,
% 1.73/1.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_C @ X0 @ sk_B) = (sk_A)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['25', '27'])).
% 1.73/1.95  thf('163', plain,
% 1.73/1.95      (![X1 : $i, X3 : $i]:
% 1.73/1.95         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.95  thf('164', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r2_hidden @ sk_A @ X0)
% 1.73/1.95          | (r1_tarski @ sk_B @ X0)
% 1.73/1.95          | (r1_tarski @ sk_B @ X0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['162', '163'])).
% 1.73/1.95  thf('165', plain,
% 1.73/1.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.73/1.95      inference('simplify', [status(thm)], ['164'])).
% 1.73/1.95  thf('166', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r2_hidden @ sk_A @ X0)
% 1.73/1.95          | (r1_tarski @ sk_B @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ X0)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['161', '165'])).
% 1.73/1.95  thf('167', plain,
% 1.73/1.95      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 1.73/1.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.95  thf('168', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r2_hidden @ sk_A @ X0)
% 1.73/1.95          | (r1_tarski @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['166', '167'])).
% 1.73/1.95  thf('169', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('170', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('171', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['146', '149'])).
% 1.73/1.95  thf('172', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r2_hidden @ (k3_tarski @ sk_B) @ X0)
% 1.73/1.95          | (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 1.73/1.95  thf('173', plain,
% 1.73/1.95      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 1.73/1.95        | (r2_hidden @ (k3_tarski @ sk_B) @ sk_C_2))),
% 1.73/1.95      inference('sup+', [status(thm)], ['154', '172'])).
% 1.73/1.95  thf('174', plain,
% 1.73/1.95      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.73/1.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.73/1.95  thf('175', plain,
% 1.73/1.95      (![X10 : $i, X12 : $i]:
% 1.73/1.95         (((X10) = (X12))
% 1.73/1.95          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.95          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.95  thf('176', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.73/1.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['174', '175'])).
% 1.73/1.95  thf('177', plain,
% 1.73/1.95      (((r2_hidden @ (k3_tarski @ sk_B) @ sk_C_2)
% 1.73/1.95        | ((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['173', '176'])).
% 1.73/1.95  thf('178', plain,
% 1.73/1.95      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.73/1.95      inference('simplify', [status(thm)], ['164'])).
% 1.73/1.95  thf('179', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['105', '128'])).
% 1.73/1.95  thf('180', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r1_tarski @ sk_B @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 1.73/1.95      inference('demod', [status(thm)], ['178', '179'])).
% 1.73/1.95  thf('181', plain,
% 1.73/1.95      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_2)) | (r1_tarski @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('sup-', [status(thm)], ['177', '180'])).
% 1.73/1.95  thf('182', plain,
% 1.73/1.95      (![X10 : $i, X12 : $i]:
% 1.73/1.95         (((X10) = (X12))
% 1.73/1.95          | ~ (r1_tarski @ X12 @ X10)
% 1.73/1.95          | ~ (r1_tarski @ X10 @ X12))),
% 1.73/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.95  thf('183', plain,
% 1.73/1.95      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_2))
% 1.73/1.95        | ~ (r1_tarski @ sk_C_2 @ sk_B)
% 1.73/1.95        | ((sk_C_2) = (sk_B)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['181', '182'])).
% 1.73/1.95  thf('184', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B)))),
% 1.73/1.95      inference('demod', [status(thm)], ['147', '148'])).
% 1.73/1.95  thf('185', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['146', '149'])).
% 1.73/1.95  thf('186', plain, (((sk_C_2) != (sk_B))),
% 1.73/1.95      inference('demod', [status(thm)], ['184', '185'])).
% 1.73/1.95  thf('187', plain,
% 1.73/1.95      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_2))
% 1.73/1.95        | ~ (r1_tarski @ sk_C_2 @ sk_B))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['183', '186'])).
% 1.73/1.95  thf('188', plain,
% 1.73/1.95      (![X1 : $i, X3 : $i]:
% 1.73/1.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.95  thf('189', plain,
% 1.73/1.95      (((k1_tarski @ (k3_tarski @ sk_B)) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['141', '142'])).
% 1.73/1.95  thf('190', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['146', '149'])).
% 1.73/1.95  thf('191', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['189', '190'])).
% 1.73/1.95  thf('192', plain,
% 1.73/1.95      (![X27 : $i, X28 : $i]:
% 1.73/1.95         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.95           = (k5_xboole_0 @ X27 @ 
% 1.73/1.95              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.95      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.95  thf('193', plain,
% 1.73/1.95      (((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.73/1.95         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['191', '192'])).
% 1.73/1.95  thf('194', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['151', '152'])).
% 1.73/1.95  thf('195', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('196', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.73/1.95  thf('197', plain,
% 1.73/1.95      (![X27 : $i, X28 : $i]:
% 1.73/1.95         ((k3_xboole_0 @ X27 @ X28)
% 1.73/1.95           = (k5_xboole_0 @ X27 @ 
% 1.73/1.95              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 1.73/1.95      inference('demod', [status(thm)], ['1', '2'])).
% 1.73/1.95  thf('198', plain,
% 1.73/1.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.73/1.95         ((r2_hidden @ X6 @ X7)
% 1.73/1.95          | (r2_hidden @ X6 @ X8)
% 1.73/1.95          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.73/1.95      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.73/1.95  thf('199', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.95          | (r2_hidden @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.73/1.95          | (r2_hidden @ X2 @ X1))),
% 1.73/1.95      inference('sup-', [status(thm)], ['197', '198'])).
% 1.73/1.95  thf('200', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X0 @ sk_C_2)
% 1.73/1.95          | (r2_hidden @ X0 @ sk_B)
% 1.73/1.95          | (r2_hidden @ X0 @ 
% 1.73/1.95             (k5_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 1.73/1.95      inference('sup-', [status(thm)], ['196', '199'])).
% 1.73/1.95  thf('201', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['189', '190'])).
% 1.73/1.95  thf('202', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['151', '152'])).
% 1.73/1.95  thf('203', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X0 @ sk_C_2)
% 1.73/1.95          | (r2_hidden @ X0 @ sk_B)
% 1.73/1.95          | (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ sk_C_2)))),
% 1.73/1.95      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.73/1.95  thf('204', plain,
% 1.73/1.95      (((k5_xboole_0 @ sk_B @ sk_C_2) = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['130', '150', '153'])).
% 1.73/1.95  thf('205', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X0 @ sk_C_2)
% 1.73/1.95          | (r2_hidden @ X0 @ sk_B)
% 1.73/1.95          | (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 1.73/1.95      inference('demod', [status(thm)], ['203', '204'])).
% 1.73/1.95  thf('206', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.73/1.95  thf('207', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.73/1.95          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('clc', [status(thm)], ['48', '51'])).
% 1.73/1.95  thf('208', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         (~ (r2_hidden @ X0 @ sk_C_2)
% 1.73/1.95          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 1.73/1.95      inference('sup-', [status(thm)], ['206', '207'])).
% 1.73/1.95  thf('209', plain,
% 1.73/1.95      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.73/1.95      inference('clc', [status(thm)], ['205', '208'])).
% 1.73/1.95  thf('210', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((r1_tarski @ sk_C_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B))),
% 1.73/1.95      inference('sup-', [status(thm)], ['188', '209'])).
% 1.73/1.95  thf('211', plain,
% 1.73/1.95      (![X1 : $i, X3 : $i]:
% 1.73/1.95         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.95  thf('212', plain,
% 1.73/1.95      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 1.73/1.95      inference('sup-', [status(thm)], ['210', '211'])).
% 1.73/1.95  thf('213', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 1.73/1.95      inference('simplify', [status(thm)], ['212'])).
% 1.73/1.95  thf('214', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['187', '213'])).
% 1.73/1.95  thf('215', plain,
% 1.73/1.95      (![X13 : $i, X14 : $i]:
% 1.73/1.95         ((k4_xboole_0 @ X13 @ X14)
% 1.73/1.95           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.73/1.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.95  thf('216', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('217', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((k3_xboole_0 @ X1 @ X0)
% 1.73/1.95           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('sup+', [status(thm)], ['215', '216'])).
% 1.73/1.95  thf('218', plain,
% 1.73/1.95      (((k3_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.73/1.95      inference('sup+', [status(thm)], ['214', '217'])).
% 1.73/1.95  thf('219', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2))),
% 1.73/1.95      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.73/1.95  thf('220', plain,
% 1.73/1.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['72', '73'])).
% 1.73/1.95  thf('221', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.73/1.95      inference('sup-', [status(thm)], ['56', '59'])).
% 1.73/1.95  thf('222', plain, (((sk_C_2) = (k1_xboole_0))),
% 1.73/1.95      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 1.73/1.95  thf('223', plain,
% 1.73/1.95      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.73/1.95      inference('split', [status(esa)], ['120'])).
% 1.73/1.95  thf('224', plain,
% 1.73/1.95      ((((k1_xboole_0) = (sk_B))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('simplify', [status(thm)], ['122'])).
% 1.73/1.95  thf('225', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.73/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.95  thf('226', plain,
% 1.73/1.95      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 1.73/1.95         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('sup+', [status(thm)], ['224', '225'])).
% 1.73/1.95  thf('227', plain,
% 1.73/1.95      (![X0 : $i]:
% 1.73/1.95         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['71', '74', '83', '84'])).
% 1.73/1.95  thf('228', plain,
% 1.73/1.95      ((((k1_xboole_0) = (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))
% 1.73/1.95         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('sup+', [status(thm)], ['226', '227'])).
% 1.73/1.95  thf('229', plain,
% 1.73/1.95      (![X0 : $i, X1 : $i]:
% 1.73/1.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.73/1.95      inference('demod', [status(thm)], ['7', '13'])).
% 1.73/1.95  thf('230', plain,
% 1.73/1.95      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0)))
% 1.73/1.95         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('sup+', [status(thm)], ['228', '229'])).
% 1.73/1.95  thf('231', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.73/1.95      inference('sup+', [status(thm)], ['91', '97'])).
% 1.73/1.95  thf('232', plain,
% 1.73/1.95      ((((k1_tarski @ sk_A) = (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.73/1.95      inference('demod', [status(thm)], ['230', '231'])).
% 1.73/1.95  thf('233', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.73/1.95      inference('simpl_trail', [status(thm)], ['107', '127'])).
% 1.73/1.95  thf('234', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['232', '233'])).
% 1.73/1.95  thf('235', plain,
% 1.73/1.95      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.73/1.95      inference('split', [status(esa)], ['120'])).
% 1.73/1.95  thf('236', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.73/1.95      inference('sat_resolution*', [status(thm)], ['234', '235'])).
% 1.73/1.95  thf('237', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.73/1.95      inference('simpl_trail', [status(thm)], ['223', '236'])).
% 1.73/1.95  thf('238', plain, ($false),
% 1.73/1.95      inference('simplify_reflect-', [status(thm)], ['222', '237'])).
% 1.73/1.95  
% 1.73/1.95  % SZS output end Refutation
% 1.73/1.95  
% 1.73/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
