%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xv11BwnH58

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  159 (2081 expanded)
%              Number of leaves         :   28 ( 555 expanded)
%              Depth                    :   34
%              Number of atoms          : 1128 (24897 expanded)
%              Number of equality atoms :  192 (5462 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B_1 )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X56
        = ( k1_tarski @ X55 ) )
      | ( X56 = k1_xboole_0 )
      | ~ ( r1_tarski @ X56 @ ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('39',plain,(
    ! [X21: $i,X24: $i] :
      ( r2_hidden @ X21 @ ( k2_tarski @ X24 @ X21 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X60: $i,X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X62 @ X63 )
      | ~ ( r2_hidden @ X60 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B_1 )
        = ( k5_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('57',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_B_1 @ sk_C ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B_1 @ X1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('69',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ sk_B_1 ) )
        = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','76'])).

thf('78',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','81'])).

thf('83',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('89',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('90',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['85','87','91'])).

thf('93',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['84','92'])).

thf('94',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','93'])).

thf('95',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('96',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','96'])).

thf('98',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','97'])).

thf('99',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('100',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('102',plain,(
    ! [X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X23 )
      | ( X25 = X24 )
      | ( X25 = X21 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('103',plain,(
    ! [X21: $i,X24: $i,X25: $i] :
      ( ( X25 = X21 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ X25 @ ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('108',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','96'])).

thf('110',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X60: $i,X62: $i,X63: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X62 @ X63 )
      | ~ ( r2_hidden @ X60 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','112'])).

thf('114',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['100','105'])).

thf('115',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('116',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','96'])).

thf('118',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('120',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
      = sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','120'])).

thf('122',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','121'])).

thf('123',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['84','92'])).

thf('124',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','124'])).

thf('127',plain,
    ( sk_C
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','125','126'])).

thf('128',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['84','92'])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xv11BwnH58
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.22/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.22/1.41  % Solved by: fo/fo7.sh
% 1.22/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.41  % done 1796 iterations in 0.997s
% 1.22/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.22/1.41  % SZS output start Refutation
% 1.22/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.22/1.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.22/1.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.22/1.41  thf(sk_B_type, type, sk_B: $i > $i).
% 1.22/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.22/1.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.22/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.22/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.22/1.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.22/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.22/1.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.22/1.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.22/1.41  thf(t43_zfmisc_1, conjecture,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.22/1.41          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.22/1.41          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.22/1.41          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.22/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.41    (~( ![A:$i,B:$i,C:$i]:
% 1.22/1.41        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.22/1.41             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.22/1.41             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.22/1.41             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.22/1.41    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.22/1.41  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf(t7_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.22/1.41  thf('1', plain,
% 1.22/1.41      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 1.22/1.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.22/1.41  thf('2', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.22/1.41      inference('sup+', [status(thm)], ['0', '1'])).
% 1.22/1.41  thf(t12_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.22/1.41  thf('3', plain,
% 1.22/1.41      (![X9 : $i, X10 : $i]:
% 1.22/1.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.22/1.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.22/1.41  thf('4', plain,
% 1.22/1.41      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.22/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.22/1.41  thf(t98_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.22/1.41  thf('5', plain,
% 1.22/1.41      (![X19 : $i, X20 : $i]:
% 1.22/1.41         ((k2_xboole_0 @ X19 @ X20)
% 1.22/1.41           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.22/1.41  thf(t92_xboole_1, axiom,
% 1.22/1.41    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.22/1.41  thf('6', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.22/1.41  thf(t91_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.22/1.41       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.22/1.41  thf('7', plain,
% 1.22/1.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.22/1.41           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.22/1.41  thf('8', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.22/1.41           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['6', '7'])).
% 1.22/1.41  thf('9', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.22/1.41  thf('10', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.22/1.41           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['6', '7'])).
% 1.22/1.41  thf('11', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.41      inference('sup+', [status(thm)], ['9', '10'])).
% 1.22/1.41  thf(t5_boole, axiom,
% 1.22/1.41    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.22/1.41  thf('12', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.22/1.41      inference('cnf', [status(esa)], [t5_boole])).
% 1.22/1.41  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.22/1.41      inference('demod', [status(thm)], ['11', '12'])).
% 1.22/1.41  thf('14', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('demod', [status(thm)], ['8', '13'])).
% 1.22/1.41  thf('15', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ X0 @ X1)
% 1.22/1.41           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['5', '14'])).
% 1.22/1.41  thf('16', plain,
% 1.22/1.41      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.22/1.41         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['4', '15'])).
% 1.22/1.41  thf('17', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('18', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ X0 @ X1)
% 1.22/1.41           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['5', '14'])).
% 1.22/1.41  thf('19', plain,
% 1.22/1.41      (((k4_xboole_0 @ sk_C @ sk_B_1)
% 1.22/1.41         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['17', '18'])).
% 1.22/1.41  thf('20', plain,
% 1.22/1.41      (((k4_xboole_0 @ sk_C @ sk_B_1)
% 1.22/1.41         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.22/1.41      inference('sup+', [status(thm)], ['16', '19'])).
% 1.22/1.41  thf(t2_boole, axiom,
% 1.22/1.41    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.22/1.41  thf('21', plain,
% 1.22/1.41      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t2_boole])).
% 1.22/1.41  thf(t100_xboole_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.22/1.41  thf('22', plain,
% 1.22/1.41      (![X7 : $i, X8 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ X7 @ X8)
% 1.22/1.41           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.41  thf('23', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.41      inference('sup+', [status(thm)], ['21', '22'])).
% 1.22/1.41  thf('24', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.22/1.41      inference('cnf', [status(esa)], [t5_boole])).
% 1.22/1.41  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.22/1.41      inference('sup+', [status(thm)], ['23', '24'])).
% 1.22/1.41  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('27', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.22/1.41      inference('sup+', [status(thm)], ['0', '1'])).
% 1.22/1.41  thf(l3_zfmisc_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.22/1.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.22/1.41  thf('28', plain,
% 1.22/1.41      (![X55 : $i, X56 : $i]:
% 1.22/1.41         (((X56) = (k1_tarski @ X55))
% 1.22/1.41          | ((X56) = (k1_xboole_0))
% 1.22/1.41          | ~ (r1_tarski @ X56 @ (k1_tarski @ X55)))),
% 1.22/1.41      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.22/1.41  thf('29', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['27', '28'])).
% 1.22/1.41  thf(t7_xboole_0, axiom,
% 1.22/1.41    (![A:$i]:
% 1.22/1.41     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.22/1.41          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.22/1.41  thf('30', plain,
% 1.22/1.41      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.22/1.41      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.41  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('32', plain,
% 1.22/1.41      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.22/1.41      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.41  thf(d3_xboole_0, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.22/1.41       ( ![D:$i]:
% 1.22/1.41         ( ( r2_hidden @ D @ C ) <=>
% 1.22/1.41           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.22/1.41  thf('33', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X0 @ X1)
% 1.22/1.41          | (r2_hidden @ X0 @ X2)
% 1.22/1.41          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.22/1.41  thf('34', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.22/1.41         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.22/1.41      inference('simplify', [status(thm)], ['33'])).
% 1.22/1.41  thf('35', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (((X0) = (k1_xboole_0))
% 1.22/1.41          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['32', '34'])).
% 1.22/1.41  thf('36', plain,
% 1.22/1.41      (((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 1.22/1.41        | ((sk_C) = (k1_xboole_0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['31', '35'])).
% 1.22/1.41  thf(t69_enumset1, axiom,
% 1.22/1.41    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.22/1.41  thf('37', plain,
% 1.22/1.41      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.22/1.41      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.41  thf(d2_tarski, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.22/1.41       ( ![D:$i]:
% 1.22/1.41         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.22/1.41  thf('38', plain,
% 1.22/1.41      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.22/1.41         (((X22) != (X21))
% 1.22/1.41          | (r2_hidden @ X22 @ X23)
% 1.22/1.41          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d2_tarski])).
% 1.22/1.41  thf('39', plain,
% 1.22/1.41      (![X21 : $i, X24 : $i]: (r2_hidden @ X21 @ (k2_tarski @ X24 @ X21))),
% 1.22/1.41      inference('simplify', [status(thm)], ['38'])).
% 1.22/1.41  thf('40', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.22/1.41      inference('sup+', [status(thm)], ['37', '39'])).
% 1.22/1.41  thf(t38_zfmisc_1, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.22/1.41       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.22/1.41  thf('41', plain,
% 1.22/1.41      (![X60 : $i, X62 : $i, X63 : $i]:
% 1.22/1.41         ((r1_tarski @ (k2_tarski @ X60 @ X62) @ X63)
% 1.22/1.41          | ~ (r2_hidden @ X62 @ X63)
% 1.22/1.41          | ~ (r2_hidden @ X60 @ X63))),
% 1.22/1.41      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.22/1.41  thf('42', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.22/1.41          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['40', '41'])).
% 1.22/1.41  thf('43', plain,
% 1.22/1.41      ((((sk_C) = (k1_xboole_0))
% 1.22/1.41        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['36', '42'])).
% 1.22/1.41  thf('44', plain,
% 1.22/1.41      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('45', plain,
% 1.22/1.41      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.22/1.41      inference('split', [status(esa)], ['44'])).
% 1.22/1.41  thf('46', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['27', '28'])).
% 1.22/1.41  thf('47', plain,
% 1.22/1.41      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('split', [status(esa)], ['44'])).
% 1.22/1.41  thf('48', plain,
% 1.22/1.41      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['46', '47'])).
% 1.22/1.41  thf('49', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('50', plain,
% 1.22/1.41      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t2_boole])).
% 1.22/1.41  thf('51', plain,
% 1.22/1.41      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['49', '50'])).
% 1.22/1.41  thf('52', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('53', plain,
% 1.22/1.41      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('demod', [status(thm)], ['51', '52'])).
% 1.22/1.41  thf('54', plain,
% 1.22/1.41      (![X7 : $i, X8 : $i]:
% 1.22/1.41         ((k4_xboole_0 @ X7 @ X8)
% 1.22/1.41           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.41  thf('55', plain,
% 1.22/1.41      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (k5_xboole_0 @ X0 @ sk_B_1)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['53', '54'])).
% 1.22/1.41  thf('56', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('57', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.22/1.41      inference('cnf', [status(esa)], [t5_boole])).
% 1.22/1.41  thf('58', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['56', '57'])).
% 1.22/1.41  thf('59', plain,
% 1.22/1.41      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['55', '58'])).
% 1.22/1.41  thf('60', plain,
% 1.22/1.41      (![X19 : $i, X20 : $i]:
% 1.22/1.41         ((k2_xboole_0 @ X19 @ X20)
% 1.22/1.41           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.22/1.41  thf('61', plain,
% 1.22/1.41      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ sk_B_1 @ X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['59', '60'])).
% 1.22/1.41  thf('62', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('63', plain,
% 1.22/1.41      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_C)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['61', '62'])).
% 1.22/1.41  thf('64', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.22/1.41  thf('65', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['56', '57'])).
% 1.22/1.41  thf('66', plain,
% 1.22/1.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.22/1.41           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.22/1.41  thf('67', plain,
% 1.22/1.41      ((![X0 : $i, X1 : $i]:
% 1.22/1.41          ((k5_xboole_0 @ X0 @ X1)
% 1.22/1.41            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B_1 @ X1))))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['65', '66'])).
% 1.22/1.41  thf('68', plain,
% 1.22/1.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.22/1.41           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.22/1.41  thf('69', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.22/1.41      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.22/1.41  thf('70', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.22/1.41           = (k1_xboole_0))),
% 1.22/1.41      inference('sup+', [status(thm)], ['68', '69'])).
% 1.22/1.41  thf('71', plain,
% 1.22/1.41      ((![X0 : $i]:
% 1.22/1.41          ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['67', '70'])).
% 1.22/1.41  thf('72', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['56', '57'])).
% 1.22/1.41  thf('73', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('74', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.22/1.41  thf('75', plain,
% 1.22/1.41      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.41         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.22/1.41           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.22/1.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.22/1.41  thf('76', plain,
% 1.22/1.41      ((![X0 : $i, X1 : $i]:
% 1.22/1.41          ((k5_xboole_0 @ sk_B_1 @ X0)
% 1.22/1.41            = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['74', '75'])).
% 1.22/1.41  thf('77', plain,
% 1.22/1.41      ((![X0 : $i]:
% 1.22/1.41          ((k5_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['64', '76'])).
% 1.22/1.41  thf('78', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('79', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ X0 @ sk_B_1)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('demod', [status(thm)], ['77', '78'])).
% 1.22/1.41  thf('80', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['56', '57'])).
% 1.22/1.41  thf('81', plain,
% 1.22/1.41      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('demod', [status(thm)], ['79', '80'])).
% 1.22/1.41  thf('82', plain,
% 1.22/1.41      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('demod', [status(thm)], ['63', '81'])).
% 1.22/1.41  thf('83', plain,
% 1.22/1.41      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('84', plain,
% 1.22/1.41      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('split', [status(esa)], ['83'])).
% 1.22/1.41  thf('85', plain,
% 1.22/1.41      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.22/1.41      inference('split', [status(esa)], ['83'])).
% 1.22/1.41  thf('86', plain,
% 1.22/1.41      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('87', plain,
% 1.22/1.41      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('split', [status(esa)], ['86'])).
% 1.22/1.41  thf('88', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('simplify', [status(thm)], ['48'])).
% 1.22/1.41  thf('89', plain,
% 1.22/1.41      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.22/1.41      inference('split', [status(esa)], ['83'])).
% 1.22/1.41  thf('90', plain,
% 1.22/1.41      ((((sk_B_1) != (sk_B_1)))
% 1.22/1.41         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.22/1.41             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['88', '89'])).
% 1.22/1.41  thf('91', plain,
% 1.22/1.41      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('simplify', [status(thm)], ['90'])).
% 1.22/1.41  thf('92', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('sat_resolution*', [status(thm)], ['85', '87', '91'])).
% 1.22/1.41  thf('93', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['84', '92'])).
% 1.22/1.41  thf('94', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['82', '93'])).
% 1.22/1.41  thf('95', plain,
% 1.22/1.41      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.22/1.41      inference('split', [status(esa)], ['44'])).
% 1.22/1.41  thf('96', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 1.22/1.41      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 1.22/1.41  thf('97', plain, (((sk_C) != (k1_xboole_0))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['45', '96'])).
% 1.22/1.41  thf('98', plain,
% 1.22/1.41      ((r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ (k1_tarski @ sk_A))),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['43', '97'])).
% 1.22/1.41  thf('99', plain,
% 1.22/1.41      (![X60 : $i, X61 : $i, X62 : $i]:
% 1.22/1.41         ((r2_hidden @ X60 @ X61)
% 1.22/1.41          | ~ (r1_tarski @ (k2_tarski @ X60 @ X62) @ X61))),
% 1.22/1.41      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.22/1.41  thf('100', plain, ((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 1.22/1.41      inference('sup-', [status(thm)], ['98', '99'])).
% 1.22/1.41  thf('101', plain,
% 1.22/1.41      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.22/1.41      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.41  thf('102', plain,
% 1.22/1.41      (![X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X25 @ X23)
% 1.22/1.41          | ((X25) = (X24))
% 1.22/1.41          | ((X25) = (X21))
% 1.22/1.41          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 1.22/1.41      inference('cnf', [status(esa)], [d2_tarski])).
% 1.22/1.41  thf('103', plain,
% 1.22/1.41      (![X21 : $i, X24 : $i, X25 : $i]:
% 1.22/1.41         (((X25) = (X21))
% 1.22/1.41          | ((X25) = (X24))
% 1.22/1.41          | ~ (r2_hidden @ X25 @ (k2_tarski @ X24 @ X21)))),
% 1.22/1.41      inference('simplify', [status(thm)], ['102'])).
% 1.22/1.41  thf('104', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['101', '103'])).
% 1.22/1.41  thf('105', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i]:
% 1.22/1.41         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.22/1.41      inference('simplify', [status(thm)], ['104'])).
% 1.22/1.41  thf('106', plain, (((sk_B @ sk_C) = (sk_A))),
% 1.22/1.41      inference('sup-', [status(thm)], ['100', '105'])).
% 1.22/1.41  thf('107', plain,
% 1.22/1.41      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.22/1.41      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.41  thf('108', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['106', '107'])).
% 1.22/1.41  thf('109', plain, (((sk_C) != (k1_xboole_0))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['45', '96'])).
% 1.22/1.41  thf('110', plain, ((r2_hidden @ sk_A @ sk_C)),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 1.22/1.41  thf('111', plain,
% 1.22/1.41      (![X60 : $i, X62 : $i, X63 : $i]:
% 1.22/1.41         ((r1_tarski @ (k2_tarski @ X60 @ X62) @ X63)
% 1.22/1.41          | ~ (r2_hidden @ X62 @ X63)
% 1.22/1.41          | ~ (r2_hidden @ X60 @ X63))),
% 1.22/1.41      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.22/1.41  thf('112', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X0 @ sk_C)
% 1.22/1.41          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C))),
% 1.22/1.41      inference('sup-', [status(thm)], ['110', '111'])).
% 1.22/1.41  thf('113', plain,
% 1.22/1.41      ((((sk_C) = (k1_xboole_0))
% 1.22/1.41        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ sk_C))),
% 1.22/1.41      inference('sup-', [status(thm)], ['30', '112'])).
% 1.22/1.41  thf('114', plain, (((sk_B @ sk_C) = (sk_A))),
% 1.22/1.41      inference('sup-', [status(thm)], ['100', '105'])).
% 1.22/1.41  thf('115', plain,
% 1.22/1.41      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.22/1.41      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.41  thf('116', plain,
% 1.22/1.41      ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C))),
% 1.22/1.41      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.22/1.41  thf('117', plain, (((sk_C) != (k1_xboole_0))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['45', '96'])).
% 1.22/1.41  thf('118', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 1.22/1.41  thf('119', plain,
% 1.22/1.41      (![X9 : $i, X10 : $i]:
% 1.22/1.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.22/1.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.22/1.41  thf('120', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C) = (sk_C))),
% 1.22/1.41      inference('sup-', [status(thm)], ['118', '119'])).
% 1.22/1.41  thf('121', plain,
% 1.22/1.41      ((((k2_xboole_0 @ sk_B_1 @ sk_C) = (sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['29', '120'])).
% 1.22/1.41  thf('122', plain,
% 1.22/1.41      ((((k1_tarski @ sk_A) = (sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.22/1.41      inference('sup+', [status(thm)], ['26', '121'])).
% 1.22/1.41  thf('123', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['84', '92'])).
% 1.22/1.41  thf('124', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 1.22/1.41  thf('125', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0))),
% 1.22/1.41      inference('demod', [status(thm)], ['25', '124'])).
% 1.22/1.41  thf('126', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0))),
% 1.22/1.41      inference('demod', [status(thm)], ['25', '124'])).
% 1.22/1.41  thf('127', plain, (((sk_C) = (k1_tarski @ sk_A))),
% 1.22/1.41      inference('demod', [status(thm)], ['20', '125', '126'])).
% 1.22/1.41  thf('128', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 1.22/1.41      inference('simpl_trail', [status(thm)], ['84', '92'])).
% 1.22/1.41  thf('129', plain, ($false),
% 1.22/1.41      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 1.22/1.41  
% 1.22/1.41  % SZS output end Refutation
% 1.22/1.41  
% 1.22/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
