%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQC4vaZKPm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (1825 expanded)
%              Number of leaves         :   28 ( 491 expanded)
%              Depth                    :   32
%              Number of atoms          : 1066 (21549 expanded)
%              Number of equality atoms :  180 (4708 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
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
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ ( k1_tarski @ X56 ) )
      | ( X55
       != ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('32',plain,(
    ! [X56: $i] :
      ( r1_tarski @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X56 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('51',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B_1 @ X1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ sk_B_1 ) )
        = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('71',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_1 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','79'])).

thf('81',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('87',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('88',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','85','89'])).

thf('91',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('92',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['80','91'])).

thf('93',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('94',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','94'])).

thf('96',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['47','95'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('97',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('98',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('101',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','94'])).

thf('103',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('105',plain,(
    ! [X59: $i,X61: $i,X62: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X59 @ X61 ) @ X62 )
      | ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r2_hidden @ X59 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ ( sk_B @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['96','98'])).

thf('109',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','94'])).

thf('112',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('114',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','114'])).

thf('116',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','115'])).

thf('117',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('118',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B_1 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','118'])).

thf('121',plain,
    ( sk_C_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','119','120'])).

thf('122',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQC4vaZKPm
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.20/2.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.20/2.38  % Solved by: fo/fo7.sh
% 2.20/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.20/2.38  % done 2727 iterations in 1.924s
% 2.20/2.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.20/2.38  % SZS output start Refutation
% 2.20/2.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.20/2.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.20/2.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.20/2.38  thf(sk_B_type, type, sk_B: $i > $i).
% 2.20/2.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.20/2.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.20/2.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.20/2.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.20/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.20/2.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.20/2.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.20/2.38  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.20/2.38  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.20/2.38  thf(t43_zfmisc_1, conjecture,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.20/2.38          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.20/2.38          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.20/2.38          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.20/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.20/2.38    (~( ![A:$i,B:$i,C:$i]:
% 2.20/2.38        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.20/2.38             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.20/2.38             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.20/2.38             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 2.20/2.38    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 2.20/2.38  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(t7_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.20/2.38  thf('1', plain,
% 2.20/2.38      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.20/2.38  thf('2', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 2.20/2.38      inference('sup+', [status(thm)], ['0', '1'])).
% 2.20/2.38  thf(t12_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.20/2.38  thf('3', plain,
% 2.20/2.38      (![X9 : $i, X10 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('4', plain,
% 2.20/2.38      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['2', '3'])).
% 2.20/2.38  thf(t98_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.20/2.38  thf('5', plain,
% 2.20/2.38      (![X19 : $i, X20 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ X19 @ X20)
% 2.20/2.38           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.20/2.38  thf(t92_xboole_1, axiom,
% 2.20/2.38    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.20/2.38  thf('6', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.20/2.38  thf(t91_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.20/2.38       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.20/2.38  thf('7', plain,
% 2.20/2.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.20/2.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.20/2.38  thf('8', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.20/2.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('9', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.20/2.38  thf('10', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.20/2.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('11', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['9', '10'])).
% 2.20/2.38  thf(t5_boole, axiom,
% 2.20/2.38    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.20/2.38  thf('12', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.20/2.38      inference('cnf', [status(esa)], [t5_boole])).
% 2.20/2.38  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.20/2.38      inference('demod', [status(thm)], ['11', '12'])).
% 2.20/2.38  thf('14', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('demod', [status(thm)], ['8', '13'])).
% 2.20/2.38  thf('15', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k4_xboole_0 @ X0 @ X1)
% 2.20/2.38           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['5', '14'])).
% 2.20/2.38  thf('16', plain,
% 2.20/2.38      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 2.20/2.38         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['4', '15'])).
% 2.20/2.38  thf('17', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('18', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k4_xboole_0 @ X0 @ X1)
% 2.20/2.38           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['5', '14'])).
% 2.20/2.38  thf('19', plain,
% 2.20/2.38      (((k4_xboole_0 @ sk_C_1 @ sk_B_1)
% 2.20/2.38         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['17', '18'])).
% 2.20/2.38  thf('20', plain,
% 2.20/2.38      (((k4_xboole_0 @ sk_C_1 @ sk_B_1)
% 2.20/2.38         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 2.20/2.38      inference('sup+', [status(thm)], ['16', '19'])).
% 2.20/2.38  thf(t2_boole, axiom,
% 2.20/2.38    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.20/2.38  thf('21', plain,
% 2.20/2.38      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t2_boole])).
% 2.20/2.38  thf(t100_xboole_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.20/2.38  thf('22', plain,
% 2.20/2.38      (![X7 : $i, X8 : $i]:
% 2.20/2.38         ((k4_xboole_0 @ X7 @ X8)
% 2.20/2.38           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.20/2.38  thf('23', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['21', '22'])).
% 2.20/2.38  thf('24', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.20/2.38      inference('cnf', [status(esa)], [t5_boole])).
% 2.20/2.38  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['23', '24'])).
% 2.20/2.38  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('27', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 2.20/2.38      inference('sup+', [status(thm)], ['0', '1'])).
% 2.20/2.38  thf(l3_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.20/2.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.20/2.38  thf('28', plain,
% 2.20/2.38      (![X54 : $i, X55 : $i]:
% 2.20/2.38         (((X55) = (k1_tarski @ X54))
% 2.20/2.38          | ((X55) = (k1_xboole_0))
% 2.20/2.38          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 2.20/2.38      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.20/2.38  thf('29', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['27', '28'])).
% 2.20/2.38  thf(t69_enumset1, axiom,
% 2.20/2.38    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.20/2.38  thf('30', plain,
% 2.20/2.38      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 2.20/2.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.20/2.38  thf('31', plain,
% 2.20/2.38      (![X55 : $i, X56 : $i]:
% 2.20/2.38         ((r1_tarski @ X55 @ (k1_tarski @ X56)) | ((X55) != (k1_tarski @ X56)))),
% 2.20/2.38      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.20/2.38  thf('32', plain,
% 2.20/2.38      (![X56 : $i]: (r1_tarski @ (k1_tarski @ X56) @ (k1_tarski @ X56))),
% 2.20/2.38      inference('simplify', [status(thm)], ['31'])).
% 2.20/2.38  thf('33', plain,
% 2.20/2.38      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['30', '32'])).
% 2.20/2.38  thf('34', plain,
% 2.20/2.38      (![X9 : $i, X10 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('35', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 2.20/2.38           = (k2_tarski @ X0 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['33', '34'])).
% 2.20/2.38  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(t7_xboole_0, axiom,
% 2.20/2.38    (![A:$i]:
% 2.20/2.38     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.20/2.38          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.20/2.38  thf('37', plain,
% 2.20/2.38      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.20/2.38  thf(d3_xboole_0, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.20/2.38       ( ![D:$i]:
% 2.20/2.38         ( ( r2_hidden @ D @ C ) <=>
% 2.20/2.38           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.20/2.38  thf('38', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X0 @ X1)
% 2.20/2.38          | (r2_hidden @ X0 @ X2)
% 2.20/2.38          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.20/2.38      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.20/2.38  thf('39', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.20/2.38         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 2.20/2.38      inference('simplify', [status(thm)], ['38'])).
% 2.20/2.38  thf('40', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         (((X0) = (k1_xboole_0))
% 2.20/2.38          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['37', '39'])).
% 2.20/2.38  thf('41', plain,
% 2.20/2.38      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 2.20/2.38        | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['36', '40'])).
% 2.20/2.38  thf('42', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X0 @ X3)
% 2.20/2.38          | (r2_hidden @ X0 @ X2)
% 2.20/2.38          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.20/2.38      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.20/2.38  thf('43', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.20/2.38         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.20/2.38      inference('simplify', [status(thm)], ['42'])).
% 2.20/2.38  thf('44', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (((sk_C_1) = (k1_xboole_0))
% 2.20/2.38          | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 2.20/2.38             (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['41', '43'])).
% 2.20/2.38  thf('45', plain,
% 2.20/2.38      (((r2_hidden @ (sk_B @ sk_C_1) @ (k2_tarski @ sk_A @ sk_A))
% 2.20/2.38        | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['35', '44'])).
% 2.20/2.38  thf('46', plain,
% 2.20/2.38      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 2.20/2.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.20/2.38  thf('47', plain,
% 2.20/2.38      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 2.20/2.38        | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('demod', [status(thm)], ['45', '46'])).
% 2.20/2.38  thf('48', plain,
% 2.20/2.38      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('49', plain,
% 2.20/2.38      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 2.20/2.38      inference('split', [status(esa)], ['48'])).
% 2.20/2.38  thf('50', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['27', '28'])).
% 2.20/2.38  thf('51', plain,
% 2.20/2.38      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('split', [status(esa)], ['48'])).
% 2.20/2.38  thf('52', plain,
% 2.20/2.38      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup-', [status(thm)], ['50', '51'])).
% 2.20/2.38  thf('53', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.20/2.38  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['23', '24'])).
% 2.20/2.38  thf('55', plain,
% 2.20/2.38      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['53', '54'])).
% 2.20/2.38  thf('56', plain,
% 2.20/2.38      (![X19 : $i, X20 : $i]:
% 2.20/2.38         ((k2_xboole_0 @ X19 @ X20)
% 2.20/2.38           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.20/2.38  thf('57', plain,
% 2.20/2.38      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ sk_B_1 @ X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['55', '56'])).
% 2.20/2.38  thf('58', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('59', plain,
% 2.20/2.38      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_C_1)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['57', '58'])).
% 2.20/2.38  thf('60', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.20/2.38  thf('61', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.20/2.38  thf('62', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.20/2.38      inference('cnf', [status(esa)], [t5_boole])).
% 2.20/2.38  thf('63', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['61', '62'])).
% 2.20/2.38  thf('64', plain,
% 2.20/2.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.20/2.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.20/2.38  thf('65', plain,
% 2.20/2.38      ((![X0 : $i, X1 : $i]:
% 2.20/2.38          ((k5_xboole_0 @ X0 @ X1)
% 2.20/2.38            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B_1 @ X1))))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['63', '64'])).
% 2.20/2.38  thf('66', plain,
% 2.20/2.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.20/2.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.20/2.38  thf('67', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.20/2.38  thf('68', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 2.20/2.38           = (k1_xboole_0))),
% 2.20/2.38      inference('sup+', [status(thm)], ['66', '67'])).
% 2.20/2.38  thf('69', plain,
% 2.20/2.38      ((![X0 : $i]:
% 2.20/2.38          ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['65', '68'])).
% 2.20/2.38  thf('70', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['61', '62'])).
% 2.20/2.38  thf('71', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.20/2.38  thf('72', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.20/2.38  thf('73', plain,
% 2.20/2.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.20/2.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 2.20/2.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.20/2.38  thf('74', plain,
% 2.20/2.38      ((![X0 : $i, X1 : $i]:
% 2.20/2.38          ((k5_xboole_0 @ sk_B_1 @ X0)
% 2.20/2.38            = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['72', '73'])).
% 2.20/2.38  thf('75', plain,
% 2.20/2.38      ((![X0 : $i]:
% 2.20/2.38          ((k5_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['60', '74'])).
% 2.20/2.38  thf('76', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.20/2.38  thf('77', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ X0 @ sk_B_1)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('demod', [status(thm)], ['75', '76'])).
% 2.20/2.38  thf('78', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_1) = (X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup+', [status(thm)], ['61', '62'])).
% 2.20/2.38  thf('79', plain,
% 2.20/2.38      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('demod', [status(thm)], ['77', '78'])).
% 2.20/2.38  thf('80', plain,
% 2.20/2.38      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('demod', [status(thm)], ['59', '79'])).
% 2.20/2.38  thf('81', plain,
% 2.20/2.38      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('82', plain,
% 2.20/2.38      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 2.20/2.38         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('split', [status(esa)], ['81'])).
% 2.20/2.38  thf('83', plain,
% 2.20/2.38      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('split', [status(esa)], ['81'])).
% 2.20/2.38  thf('84', plain,
% 2.20/2.38      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('85', plain,
% 2.20/2.38      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 2.20/2.38       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('split', [status(esa)], ['84'])).
% 2.20/2.38  thf('86', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.20/2.38  thf('87', plain,
% 2.20/2.38      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.20/2.38      inference('split', [status(esa)], ['81'])).
% 2.20/2.38  thf('88', plain,
% 2.20/2.38      ((((sk_B_1) != (sk_B_1)))
% 2.20/2.38         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.20/2.38             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.20/2.38      inference('sup-', [status(thm)], ['86', '87'])).
% 2.20/2.38  thf('89', plain,
% 2.20/2.38      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('simplify', [status(thm)], ['88'])).
% 2.20/2.38  thf('90', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('sat_resolution*', [status(thm)], ['83', '85', '89'])).
% 2.20/2.38  thf('91', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 2.20/2.38  thf('92', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['80', '91'])).
% 2.20/2.38  thf('93', plain,
% 2.20/2.38      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.20/2.38      inference('split', [status(esa)], ['48'])).
% 2.20/2.38  thf('94', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 2.20/2.38  thf('95', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['49', '94'])).
% 2.20/2.38  thf('96', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['47', '95'])).
% 2.20/2.38  thf(d1_tarski, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.20/2.38       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.20/2.38  thf('97', plain,
% 2.20/2.38      (![X21 : $i, X23 : $i, X24 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X24 @ X23)
% 2.20/2.38          | ((X24) = (X21))
% 2.20/2.38          | ((X23) != (k1_tarski @ X21)))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_tarski])).
% 2.20/2.38  thf('98', plain,
% 2.20/2.38      (![X21 : $i, X24 : $i]:
% 2.20/2.38         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 2.20/2.38      inference('simplify', [status(thm)], ['97'])).
% 2.20/2.38  thf('99', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['96', '98'])).
% 2.20/2.38  thf('100', plain,
% 2.20/2.38      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.20/2.38  thf('101', plain,
% 2.20/2.38      (((r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['99', '100'])).
% 2.20/2.38  thf('102', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['49', '94'])).
% 2.20/2.38  thf('103', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 2.20/2.38  thf('104', plain,
% 2.20/2.38      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.20/2.38      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.20/2.38  thf(t38_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 2.20/2.38       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 2.20/2.38  thf('105', plain,
% 2.20/2.38      (![X59 : $i, X61 : $i, X62 : $i]:
% 2.20/2.38         ((r1_tarski @ (k2_tarski @ X59 @ X61) @ X62)
% 2.20/2.38          | ~ (r2_hidden @ X61 @ X62)
% 2.20/2.38          | ~ (r2_hidden @ X59 @ X62))),
% 2.20/2.38      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.20/2.38  thf('106', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         (((X0) = (k1_xboole_0))
% 2.20/2.38          | ~ (r2_hidden @ X1 @ X0)
% 2.20/2.38          | (r1_tarski @ (k2_tarski @ X1 @ (sk_B @ X0)) @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['104', '105'])).
% 2.20/2.38  thf('107', plain,
% 2.20/2.38      (((r1_tarski @ (k2_tarski @ sk_A @ (sk_B @ sk_C_1)) @ sk_C_1)
% 2.20/2.38        | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['103', '106'])).
% 2.20/2.38  thf('108', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['96', '98'])).
% 2.20/2.38  thf('109', plain,
% 2.20/2.38      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 2.20/2.38      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.20/2.38  thf('110', plain,
% 2.20/2.38      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.20/2.38  thf('111', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['49', '94'])).
% 2.20/2.38  thf('112', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 2.20/2.38  thf('113', plain,
% 2.20/2.38      (![X9 : $i, X10 : $i]:
% 2.20/2.38         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 2.20/2.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.20/2.38  thf('114', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))),
% 2.20/2.38      inference('sup-', [status(thm)], ['112', '113'])).
% 2.20/2.38  thf('115', plain,
% 2.20/2.38      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 2.20/2.38        | ((sk_B_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['29', '114'])).
% 2.20/2.38  thf('116', plain,
% 2.20/2.38      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 2.20/2.38      inference('sup+', [status(thm)], ['26', '115'])).
% 2.20/2.38  thf('117', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 2.20/2.38  thf('118', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 2.20/2.38  thf('119', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0))),
% 2.20/2.38      inference('demod', [status(thm)], ['25', '118'])).
% 2.20/2.38  thf('120', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_B_1) = (X0))),
% 2.20/2.38      inference('demod', [status(thm)], ['25', '118'])).
% 2.20/2.38  thf('121', plain, (((sk_C_1) = (k1_tarski @ sk_A))),
% 2.20/2.38      inference('demod', [status(thm)], ['20', '119', '120'])).
% 2.20/2.38  thf('122', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 2.20/2.38      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 2.20/2.38  thf('123', plain, ($false),
% 2.20/2.38      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 2.20/2.38  
% 2.20/2.38  % SZS output end Refutation
% 2.20/2.38  
% 2.20/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
