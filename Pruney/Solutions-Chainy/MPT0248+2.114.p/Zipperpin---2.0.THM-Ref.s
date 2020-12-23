%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UXs0Q9aZ5H

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:34 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  143 (1813 expanded)
%              Number of leaves         :   25 ( 491 expanded)
%              Depth                    :   26
%              Number of atoms          : 1009 (21284 expanded)
%              Number of equality atoms :  168 (4618 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35
        = ( k1_tarski @ X34 ) )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('19',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ X32 )
        = X32 )
      | ~ ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ ( k1_tarski @ X36 ) )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('42',plain,(
    ! [X36: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','50'])).

thf('52',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('53',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('57',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ( sk_C_1 = sk_B_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','55','56'])).

thf('58',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('64',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('65',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','62','66'])).

thf('68',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','67'])).

thf('69',plain,
    ( ( sk_C_1 = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('71',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('74',plain,
    ( ( ( ( k3_tarski @ ( k1_tarski @ sk_C_1 ) )
        = ( k1_tarski @ sk_A ) )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C_1 = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','68'])).

thf('76',plain,
    ( ( sk_C_1 = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','68'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('78',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ sk_B_2 ) )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_tarski @ ( k1_tarski @ sk_B_2 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ sk_B_2 ) )
      = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','79'])).

thf('81',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('82',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ sk_B_2 ) )
      = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('85',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2
         != ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( sk_B_2
       != ( k3_tarski @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( sk_C_1 = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','68'])).

thf('89',plain,
    ( ( sk_C_1 = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','68'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('91',plain,
    ( ( sk_B_2
     != ( k3_tarski @ ( k1_tarski @ sk_B_2 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( sk_B_2
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','91'])).

thf('93',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('94',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['8','94'])).

thf('96',plain,(
    r2_hidden @ ( sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','95'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('97',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('98',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( sk_B_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('101',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['8','94'])).

thf('103',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('105',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('106',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('107',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_2 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    r1_tarski @ sk_B_2 @ sk_C_1 ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('113',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['0','113'])).

thf('115',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','67'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UXs0Q9aZ5H
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:26:23 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 976 iterations in 0.415s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.72/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.72/0.90  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.72/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.72/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.90  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.90  thf(t43_zfmisc_1, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.72/0.90          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.72/0.90          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.72/0.90          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.90        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.72/0.90             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.72/0.90             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.72/0.90             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.72/0.90  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t7_xboole_0, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.72/0.90          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.72/0.90  thf(d3_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.72/0.90       ( ![D:$i]:
% 0.72/0.90         ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.90           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X3 @ X4)
% 0.72/0.90          | (r2_hidden @ X3 @ X5)
% 0.72/0.90          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.72/0.90         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.72/0.90      inference('simplify', [status(thm)], ['3'])).
% 0.72/0.90  thf('5', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((X0) = (k1_xboole_0))
% 0.72/0.90          | (r2_hidden @ (sk_B_1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['2', '4'])).
% 0.72/0.90  thf('6', plain,
% 0.72/0.90      (((r2_hidden @ (sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.72/0.90        | ((sk_C_1) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['1', '5'])).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('8', plain,
% 0.72/0.90      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.72/0.90      inference('split', [status(esa)], ['7'])).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.72/0.90  thf(d1_xboole_0, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.90  thf('12', plain,
% 0.72/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.72/0.90  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t7_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.72/0.90  thf('15', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('sup+', [status(thm)], ['13', '14'])).
% 0.72/0.90  thf(l3_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.72/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X34 : $i, X35 : $i]:
% 0.72/0.90         (((X35) = (k1_tarski @ X34))
% 0.72/0.90          | ((X35) = (k1_xboole_0))
% 0.72/0.90          | ~ (r1_tarski @ X35 @ (k1_tarski @ X34)))),
% 0.72/0.90      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('split', [status(esa)], ['7'])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      (((((sk_B_2) != (sk_B_2)) | ((sk_B_2) = (k1_xboole_0))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      ((![X0 : $i]: (((sk_B_2) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['12', '20'])).
% 0.72/0.90  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_1))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.72/0.90           | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf(t69_enumset1, axiom,
% 0.72/0.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.72/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.90  thf(l51_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      (![X37 : $i, X38 : $i]:
% 0.72/0.90         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.72/0.90      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.90  thf('27', plain,
% 0.72/0.90      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.90  thf('28', plain,
% 0.72/0.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X7 @ X5)
% 0.72/0.90          | (r2_hidden @ X7 @ X6)
% 0.72/0.90          | (r2_hidden @ X7 @ X4)
% 0.72/0.90          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.72/0.90  thf('29', plain,
% 0.72/0.90      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.72/0.90         ((r2_hidden @ X7 @ X4)
% 0.72/0.90          | (r2_hidden @ X7 @ X6)
% 0.72/0.90          | ~ (r2_hidden @ X7 @ (k2_xboole_0 @ X6 @ X4)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['28'])).
% 0.72/0.90  thf('30', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0)))
% 0.72/0.90          | (r2_hidden @ X1 @ X0)
% 0.72/0.90          | (r2_hidden @ X1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['27', '29'])).
% 0.72/0.90  thf('31', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r2_hidden @ X1 @ X0)
% 0.72/0.90          | ~ (r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['26', '31'])).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.72/0.90           | ~ (v1_xboole_0 @ sk_C_1)
% 0.72/0.90           | (r2_hidden @ X0 @ sk_C_1)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['23', '32'])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.90  thf('35', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (~ (v1_xboole_0 @ sk_C_1) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('clc', [status(thm)], ['33', '34'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.72/0.90           | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.72/0.90  thf(l22_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r2_hidden @ A @ B ) =>
% 0.72/0.90       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.72/0.90  thf('38', plain,
% 0.72/0.90      (![X32 : $i, X33 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ (k1_tarski @ X33) @ X32) = (X32))
% 0.72/0.90          | ~ (r2_hidden @ X33 @ X32))),
% 0.72/0.90      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.72/0.90  thf('39', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((X0) = (k1_xboole_0))
% 0.72/0.90          | ((k2_xboole_0 @ (k1_tarski @ (sk_B_1 @ X0)) @ X0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.72/0.90  thf('40', plain,
% 0.72/0.90      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.72/0.90  thf('41', plain,
% 0.72/0.90      (![X35 : $i, X36 : $i]:
% 0.72/0.90         ((r1_tarski @ X35 @ (k1_tarski @ X36)) | ((X35) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.72/0.90  thf('42', plain,
% 0.72/0.90      (![X36 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X36))),
% 0.72/0.90      inference('simplify', [status(thm)], ['41'])).
% 0.72/0.90  thf(t12_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.72/0.90  thf('43', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['42', '43'])).
% 0.72/0.90  thf(t11_xboole_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.90         ((r1_tarski @ X10 @ X11)
% 0.72/0.90          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.72/0.90          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.72/0.90      inference('sup-', [status(thm)], ['44', '45'])).
% 0.72/0.90  thf('47', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['40', '46'])).
% 0.72/0.90  thf('48', plain,
% 0.72/0.90      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['39', '47'])).
% 0.72/0.90  thf('49', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('50', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['48', '49'])).
% 0.72/0.90  thf('51', plain,
% 0.72/0.90      (((((k1_tarski @ sk_A) = (sk_C_1))
% 0.72/0.90         | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.72/0.90         | ((sk_C_1) = (k1_xboole_0))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['36', '50'])).
% 0.72/0.90  thf('52', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf('53', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.72/0.90  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.72/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.72/0.90  thf('55', plain,
% 0.72/0.90      (((v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('56', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf('57', plain,
% 0.72/0.90      (((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_C_1) = (sk_B_2))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['51', '52', '55', '56'])).
% 0.72/0.90  thf('58', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('59', plain,
% 0.72/0.90      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.72/0.90         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('split', [status(esa)], ['58'])).
% 0.72/0.90  thf('60', plain,
% 0.72/0.90      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_2) = (k1_xboole_0)))),
% 0.72/0.90      inference('split', [status(esa)], ['58'])).
% 0.72/0.90  thf('61', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('62', plain,
% 0.72/0.90      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.72/0.90       ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('split', [status(esa)], ['61'])).
% 0.72/0.90  thf('63', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf('64', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.72/0.90      inference('split', [status(esa)], ['58'])).
% 0.72/0.90  thf('65', plain,
% 0.72/0.90      ((((sk_B_2) != (sk_B_2)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.72/0.90             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['63', '64'])).
% 0.72/0.90  thf('66', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['65'])).
% 0.72/0.90  thf('67', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sat_resolution*', [status(thm)], ['60', '62', '66'])).
% 0.72/0.90  thf('68', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['59', '67'])).
% 0.72/0.90  thf('69', plain,
% 0.72/0.90      ((((sk_C_1) = (sk_B_2))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['57', '68'])).
% 0.72/0.90  thf('70', plain,
% 0.72/0.90      (((v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('71', plain,
% 0.72/0.90      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['35', '69', '70'])).
% 0.72/0.90  thf('72', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.72/0.90           | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('73', plain,
% 0.72/0.90      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.90  thf('74', plain,
% 0.72/0.90      (((((k3_tarski @ (k1_tarski @ sk_C_1)) = (k1_tarski @ sk_A))
% 0.72/0.90         | ~ (v1_xboole_0 @ sk_C_1))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['72', '73'])).
% 0.72/0.90  thf('75', plain,
% 0.72/0.90      ((((sk_C_1) = (sk_B_2))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['57', '68'])).
% 0.72/0.90  thf('76', plain,
% 0.72/0.90      ((((sk_C_1) = (sk_B_2))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['57', '68'])).
% 0.72/0.90  thf('77', plain,
% 0.72/0.90      (((v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('78', plain,
% 0.72/0.90      ((((k3_tarski @ (k1_tarski @ sk_B_2)) = (k1_tarski @ sk_A)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.72/0.90  thf('79', plain,
% 0.72/0.90      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_tarski @ (k1_tarski @ sk_B_2))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['71', '78'])).
% 0.72/0.90  thf('80', plain,
% 0.72/0.90      ((((k3_tarski @ (k1_tarski @ sk_B_2)) = (k1_xboole_0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['9', '79'])).
% 0.72/0.90  thf('81', plain,
% 0.72/0.90      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.72/0.90  thf('82', plain,
% 0.72/0.90      ((((k3_tarski @ (k1_tarski @ sk_B_2)) = (sk_B_2)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['80', '81'])).
% 0.72/0.90  thf('83', plain,
% 0.72/0.90      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.72/0.90  thf('84', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 0.72/0.90           | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('85', plain,
% 0.72/0.90      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('split', [status(esa)], ['7'])).
% 0.72/0.90  thf('86', plain,
% 0.72/0.90      ((![X0 : $i]:
% 0.72/0.90          (((sk_B_2) != (k2_xboole_0 @ X0 @ sk_C_1)) | ~ (v1_xboole_0 @ X0)))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['84', '85'])).
% 0.72/0.90  thf('87', plain,
% 0.72/0.90      (((((sk_B_2) != (k3_tarski @ (k1_tarski @ sk_C_1)))
% 0.72/0.90         | ~ (v1_xboole_0 @ sk_C_1))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['83', '86'])).
% 0.72/0.90  thf('88', plain,
% 0.72/0.90      ((((sk_C_1) = (sk_B_2))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['57', '68'])).
% 0.72/0.90  thf('89', plain,
% 0.72/0.90      ((((sk_C_1) = (sk_B_2))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['57', '68'])).
% 0.72/0.90  thf('90', plain,
% 0.72/0.90      (((v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('91', plain,
% 0.72/0.90      ((((sk_B_2) != (k3_tarski @ (k1_tarski @ sk_B_2))))
% 0.72/0.90         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.72/0.90  thf('92', plain, ((((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['82', '91'])).
% 0.72/0.90  thf('93', plain,
% 0.72/0.90      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('split', [status(esa)], ['7'])).
% 0.72/0.90  thf('94', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.72/0.90      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.72/0.90  thf('95', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['8', '94'])).
% 0.72/0.90  thf('96', plain, ((r2_hidden @ (sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['6', '95'])).
% 0.72/0.90  thf(d1_tarski, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.72/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.72/0.90  thf('97', plain,
% 0.72/0.90      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X20 @ X19)
% 0.72/0.90          | ((X20) = (X17))
% 0.72/0.90          | ((X19) != (k1_tarski @ X17)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d1_tarski])).
% 0.72/0.90  thf('98', plain,
% 0.72/0.90      (![X17 : $i, X20 : $i]:
% 0.72/0.90         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.72/0.90  thf('99', plain, (((sk_B_1 @ sk_C_1) = (sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['96', '98'])).
% 0.72/0.90  thf('100', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((X0) = (k1_xboole_0))
% 0.72/0.90          | ((k2_xboole_0 @ (k1_tarski @ (sk_B_1 @ X0)) @ X0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.72/0.90  thf('101', plain,
% 0.72/0.90      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))
% 0.72/0.90        | ((sk_C_1) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['99', '100'])).
% 0.72/0.90  thf('102', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['8', '94'])).
% 0.72/0.90  thf('103', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.72/0.90  thf('104', plain,
% 0.72/0.90      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.72/0.90  thf('105', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('sup+', [status(thm)], ['13', '14'])).
% 0.72/0.90  thf('106', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('107', plain,
% 0.72/0.90      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['105', '106'])).
% 0.72/0.90  thf('108', plain,
% 0.72/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.90         ((r1_tarski @ X10 @ X11)
% 0.72/0.90          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.72/0.90  thf('109', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B_2 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['107', '108'])).
% 0.72/0.90  thf('110', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (r1_tarski @ sk_B_2 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['104', '109'])).
% 0.72/0.90  thf('111', plain, ((r1_tarski @ sk_B_2 @ sk_C_1)),
% 0.72/0.90      inference('sup+', [status(thm)], ['103', '110'])).
% 0.72/0.90  thf('112', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('113', plain, (((k2_xboole_0 @ sk_B_2 @ sk_C_1) = (sk_C_1))),
% 0.72/0.90      inference('sup-', [status(thm)], ['111', '112'])).
% 0.72/0.90  thf('114', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.72/0.90      inference('sup+', [status(thm)], ['0', '113'])).
% 0.72/0.90  thf('115', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['59', '67'])).
% 0.72/0.90  thf('116', plain, ($false),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
