%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeYdNe8y4m

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 321 expanded)
%              Number of leaves         :   21 (  89 expanded)
%              Depth                    :   27
%              Number of atoms          :  881 (3641 expanded)
%              Number of equality atoms :  150 ( 756 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ ( k1_tarski @ X54 ) )
      | ( X53 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X54: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X54 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ( X22 = X21 )
      | ( X22 = X18 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X18: $i,X21: $i,X22: $i] :
      ( ( X22 = X18 )
      | ( X22 = X21 )
      | ~ ( r2_hidden @ X22 @ ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

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
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
          = X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
          = X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','60'])).

thf('62',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('68',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('69',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['64','66','70'])).

thf('72',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('73',plain,
    ( ( sk_C_1 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('79',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('81',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['40','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','82'])).

thf('84',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['23','83'])).

thf('85',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('95',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','95'])).

thf('97',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('98',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','98'])).

thf('100',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['0','99'])).

thf('101',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeYdNe8y4m
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:31:31 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.34  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 389 iterations in 0.201s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(t43_zfmisc_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.47/0.65          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.47/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.65        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.47/0.65             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.47/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.47/0.65  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d3_tarski, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i]:
% 0.47/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf(l3_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.47/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X53 : $i, X54 : $i]:
% 0.47/0.65         ((r1_tarski @ X53 @ (k1_tarski @ X54)) | ((X53) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.47/0.65  thf('3', plain, (![X54 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X54))),
% 0.47/0.65      inference('simplify', [status(thm)], ['2'])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.65          | (r2_hidden @ X0 @ X2)
% 0.47/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.47/0.65          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.65          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '5'])).
% 0.47/0.66  thf(t69_enumset1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.66  thf('7', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf(d2_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.47/0.66       ( ![D:$i]:
% 0.47/0.66         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X22 @ X20)
% 0.47/0.66          | ((X22) = (X21))
% 0.47/0.66          | ((X22) = (X18))
% 0.47/0.66          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X18 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         (((X22) = (X18))
% 0.47/0.66          | ((X22) = (X21))
% 0.47/0.66          | ~ (r2_hidden @ X22 @ (k2_tarski @ X21 @ X18)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '9'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '11'])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (X1))
% 0.47/0.66          | (r1_tarski @ k1_xboole_0 @ X2)
% 0.47/0.66          | (r1_tarski @ k1_xboole_0 @ X2))),
% 0.47/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.66  thf(t12_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((X1) = (X2)) | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.66      inference('condensation', [status(thm)], ['17'])).
% 0.47/0.66  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('21', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.47/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf('24', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t7_xboole_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf(d3_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.47/0.66       ( ![D:$i]:
% 0.47/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X4 @ X5)
% 0.47/0.66          | (r2_hidden @ X4 @ X6)
% 0.47/0.66          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.47/0.66         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.47/0.66      inference('simplify', [status(thm)], ['26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.47/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['24', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('31', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf(t7_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.47/0.66          | ((sk_C_1) = (k1_xboole_0))
% 0.47/0.66          | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['31', '36'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((sk_C_1) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['39'])).
% 0.47/0.66  thf('41', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('42', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.66  thf('44', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X52 : $i, X53 : $i]:
% 0.47/0.66         (((X53) = (k1_tarski @ X52))
% 0.47/0.66          | ((X53) = (k1_xboole_0))
% 0.47/0.66          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['39'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '11'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r1_tarski @ k1_xboole_0 @ X1)
% 0.47/0.66          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ k1_xboole_0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.66      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['50', '54'])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((k2_xboole_0 @ sk_B_1 @ X0) = (X0)) | ((X0) = (k1_xboole_0))))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['49', '57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      ((![X0 : $i]: (((k2_xboole_0 @ sk_B_1 @ X0) = (X0)) | ((X0) = (sk_B_1))))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_C_1) = (sk_B_1))))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['41', '60'])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.47/0.66         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('split', [status(esa)], ['62'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.47/0.66       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.47/0.66      inference('split', [status(esa)], ['62'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      ((((sk_B_1) != (sk_B_1)))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.47/0.66             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['69'])).
% 0.47/0.66  thf('71', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['64', '66', '70'])).
% 0.47/0.66  thf('72', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      ((((sk_C_1) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['61', '72'])).
% 0.47/0.66  thf('74', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['73', '74'])).
% 0.47/0.66  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['75', '76'])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.47/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['39'])).
% 0.47/0.66  thf('79', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['39'])).
% 0.47/0.66  thf('81', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.47/0.66  thf('82', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['40', '81'])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['38', '82'])).
% 0.47/0.66  thf('84', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.47/0.66      inference('sup+', [status(thm)], ['23', '83'])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf('87', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.47/0.66          | ((sk_B_1) = (k1_xboole_0))
% 0.47/0.66          | ((X0) = (sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.66  thf('89', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | ((sk_C @ X0 @ sk_B_1) = (sk_A))
% 0.47/0.66          | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['85', '88'])).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ sk_A @ X0)
% 0.47/0.66          | ((sk_B_1) = (k1_xboole_0))
% 0.47/0.66          | (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | (r1_tarski @ sk_B_1 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | ((sk_B_1) = (k1_xboole_0))
% 0.47/0.66          | ~ (r2_hidden @ sk_A @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['91'])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['84', '92'])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('95', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.66        | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['19', '95'])).
% 0.47/0.66  thf('97', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.47/0.66  thf('98', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.47/0.66  thf('99', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['18', '98'])).
% 0.47/0.66  thf('100', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '99'])).
% 0.47/0.66  thf('101', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 0.47/0.66  thf('102', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
