%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vkKMu3iKS2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:59 EST 2020

% Result     : Theorem 29.04s
% Output     : Refutation 29.04s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 350 expanded)
%              Number of leaves         :   10 (  95 expanded)
%              Depth                    :   21
%              Number of atoms          :  890 (3778 expanded)
%              Number of equality atoms :   68 ( 325 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_B_1 )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['20','21','38'])).

thf('40',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_B_1 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_B_1 ) @ sk_A )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('55',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ sk_A )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('69',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('76',plain,(
    $false ),
    inference('sup-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vkKMu3iKS2
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 29.04/29.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.04/29.29  % Solved by: fo/fo7.sh
% 29.04/29.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.04/29.29  % done 30445 iterations in 28.831s
% 29.04/29.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.04/29.29  % SZS output start Refutation
% 29.04/29.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.04/29.29  thf(sk_B_type, type, sk_B: $i > $i).
% 29.04/29.29  thf(sk_A_type, type, sk_A: $i).
% 29.04/29.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.04/29.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 29.04/29.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 29.04/29.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.04/29.29  thf(t7_xboole_0, axiom,
% 29.04/29.29    (![A:$i]:
% 29.04/29.29     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 29.04/29.29          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 29.04/29.29  thf('0', plain,
% 29.04/29.29      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 29.04/29.29      inference('cnf', [status(esa)], [t7_xboole_0])).
% 29.04/29.29  thf(d5_xboole_0, axiom,
% 29.04/29.29    (![A:$i,B:$i,C:$i]:
% 29.04/29.29     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 29.04/29.29       ( ![D:$i]:
% 29.04/29.29         ( ( r2_hidden @ D @ C ) <=>
% 29.04/29.29           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 29.04/29.29  thf('1', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X3)
% 29.04/29.29          | (r2_hidden @ X4 @ X1)
% 29.04/29.29          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('2', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['1'])).
% 29.04/29.29  thf('3', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 29.04/29.29          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 29.04/29.29      inference('sup-', [status(thm)], ['0', '2'])).
% 29.04/29.29  thf('4', plain,
% 29.04/29.29      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 29.04/29.29      inference('cnf', [status(esa)], [t7_xboole_0])).
% 29.04/29.29  thf(t32_xboole_1, conjecture,
% 29.04/29.29    (![A:$i,B:$i]:
% 29.04/29.29     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 29.04/29.29       ( ( A ) = ( B ) ) ))).
% 29.04/29.29  thf(zf_stmt_0, negated_conjecture,
% 29.04/29.29    (~( ![A:$i,B:$i]:
% 29.04/29.29        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 29.04/29.29          ( ( A ) = ( B ) ) ) )),
% 29.04/29.29    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 29.04/29.29  thf('5', plain,
% 29.04/29.29      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 29.04/29.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.29  thf('6', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X3)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('7', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['6'])).
% 29.04/29.29  thf('8', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 29.04/29.29          | ~ (r2_hidden @ X0 @ sk_A))),
% 29.04/29.29      inference('sup-', [status(thm)], ['5', '7'])).
% 29.04/29.29  thf('9', plain,
% 29.04/29.29      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 29.04/29.29        | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ sk_A @ sk_B_1)) @ sk_A))),
% 29.04/29.29      inference('sup-', [status(thm)], ['4', '8'])).
% 29.04/29.29  thf('10', plain,
% 29.04/29.29      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 29.04/29.29        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['3', '9'])).
% 29.04/29.29  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 29.04/29.29      inference('simplify', [status(thm)], ['10'])).
% 29.04/29.29  thf('12', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('13', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X0 @ X1)
% 29.04/29.29          | (r2_hidden @ X0 @ X2)
% 29.04/29.29          | (r2_hidden @ X0 @ X3)
% 29.04/29.29          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('14', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ X0 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X0 @ X1))),
% 29.04/29.29      inference('simplify', [status(thm)], ['13'])).
% 29.04/29.29  thf('15', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 29.04/29.29          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X3)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['12', '14'])).
% 29.04/29.29  thf('16', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('17', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 29.04/29.29          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 29.04/29.29          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 29.04/29.29      inference('sup-', [status(thm)], ['15', '16'])).
% 29.04/29.29  thf('18', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 29.04/29.29          | ((X2) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 29.04/29.29      inference('simplify', [status(thm)], ['17'])).
% 29.04/29.29  thf('19', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 29.04/29.29      inference('eq_fact', [status(thm)], ['18'])).
% 29.04/29.29  thf('20', plain,
% 29.04/29.29      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_B_1)
% 29.04/29.29        | ((sk_B_1) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1))))),
% 29.04/29.29      inference('sup+', [status(thm)], ['11', '19'])).
% 29.04/29.29  thf('21', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 29.04/29.29      inference('simplify', [status(thm)], ['10'])).
% 29.04/29.29  thf('22', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('23', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 29.04/29.29      inference('eq_fact', [status(thm)], ['22'])).
% 29.04/29.29  thf('24', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('25', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['23', '24'])).
% 29.04/29.29  thf('26', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['25'])).
% 29.04/29.29  thf('27', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 29.04/29.29      inference('eq_fact', [status(thm)], ['22'])).
% 29.04/29.29  thf('28', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 29.04/29.29      inference('clc', [status(thm)], ['26', '27'])).
% 29.04/29.29  thf('29', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 29.04/29.29          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 29.04/29.29      inference('sup-', [status(thm)], ['0', '2'])).
% 29.04/29.29  thf('30', plain,
% 29.04/29.29      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 29.04/29.29      inference('cnf', [status(esa)], [t7_xboole_0])).
% 29.04/29.29  thf('31', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['6'])).
% 29.04/29.29  thf('32', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 29.04/29.29          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['30', '31'])).
% 29.04/29.29  thf('33', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 29.04/29.29          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['29', '32'])).
% 29.04/29.29  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.04/29.29      inference('simplify', [status(thm)], ['33'])).
% 29.04/29.29  thf('35', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['6'])).
% 29.04/29.29  thf('36', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['34', '35'])).
% 29.04/29.29  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 29.04/29.29      inference('condensation', [status(thm)], ['36'])).
% 29.04/29.29  thf('38', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['28', '37'])).
% 29.04/29.29  thf('39', plain,
% 29.04/29.29      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_B_1)
% 29.04/29.29        | ((sk_B_1) = (sk_A)))),
% 29.04/29.29      inference('demod', [status(thm)], ['20', '21', '38'])).
% 29.04/29.29  thf('40', plain, (((sk_A) != (sk_B_1))),
% 29.04/29.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.29  thf('41', plain,
% 29.04/29.29      ((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_B_1)),
% 29.04/29.29      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 29.04/29.29  thf('42', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('43', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ X0 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X0 @ X1))),
% 29.04/29.29      inference('simplify', [status(thm)], ['13'])).
% 29.04/29.29  thf('44', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X3)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['42', '43'])).
% 29.04/29.29  thf('45', plain,
% 29.04/29.29      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 29.04/29.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.29  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 29.04/29.29      inference('simplify', [status(thm)], ['10'])).
% 29.04/29.29  thf('47', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 29.04/29.29      inference('demod', [status(thm)], ['45', '46'])).
% 29.04/29.29  thf('48', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 29.04/29.29      inference('eq_fact', [status(thm)], ['22'])).
% 29.04/29.29  thf('49', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ X0 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X0 @ X1))),
% 29.04/29.29      inference('simplify', [status(thm)], ['13'])).
% 29.04/29.29  thf('50', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2)
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['48', '49'])).
% 29.04/29.29  thf('51', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_B_1) @ k1_xboole_0)
% 29.04/29.29          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_B_1) @ sk_A)
% 29.04/29.29          | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)))),
% 29.04/29.29      inference('sup+', [status(thm)], ['47', '50'])).
% 29.04/29.29  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 29.04/29.29      inference('condensation', [status(thm)], ['36'])).
% 29.04/29.29  thf('53', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0))
% 29.04/29.29          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_B_1) @ sk_A))),
% 29.04/29.29      inference('clc', [status(thm)], ['51', '52'])).
% 29.04/29.29  thf('54', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 29.04/29.29      inference('clc', [status(thm)], ['26', '27'])).
% 29.04/29.29  thf('55', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['6'])).
% 29.04/29.29  thf('56', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['54', '55'])).
% 29.04/29.29  thf('57', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_A)))
% 29.04/29.29          | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_A))))),
% 29.04/29.29      inference('sup-', [status(thm)], ['53', '56'])).
% 29.04/29.29  thf('58', plain,
% 29.04/29.29      (![X0 : $i]:
% 29.04/29.29         ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_A)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['57'])).
% 29.04/29.29  thf('59', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X4 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X4 @ X2)
% 29.04/29.29          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 29.04/29.29      inference('simplify', [status(thm)], ['6'])).
% 29.04/29.29  thf('60', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i]:
% 29.04/29.29         (~ (r2_hidden @ X1 @ sk_B_1)
% 29.04/29.29          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_A)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['58', '59'])).
% 29.04/29.29  thf('61', plain,
% 29.04/29.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.29         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ sk_A)
% 29.04/29.29          | ((X0) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ sk_B_1))),
% 29.04/29.29      inference('sup-', [status(thm)], ['44', '60'])).
% 29.04/29.29  thf('62', plain,
% 29.04/29.29      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 29.04/29.29        | ((sk_B_1) = (k4_xboole_0 @ sk_A @ k1_xboole_0))
% 29.04/29.29        | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 29.04/29.29      inference('sup-', [status(thm)], ['41', '61'])).
% 29.04/29.29  thf('63', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['28', '37'])).
% 29.04/29.29  thf('64', plain,
% 29.04/29.29      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 29.04/29.29        | ((sk_B_1) = (sk_A))
% 29.04/29.29        | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 29.04/29.29      inference('demod', [status(thm)], ['62', '63'])).
% 29.04/29.29  thf('65', plain,
% 29.04/29.29      ((((sk_B_1) = (sk_A))
% 29.04/29.29        | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 29.04/29.29      inference('simplify', [status(thm)], ['64'])).
% 29.04/29.29  thf('66', plain, (((sk_A) != (sk_B_1))),
% 29.04/29.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.29  thf('67', plain, ((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 29.04/29.29      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 29.04/29.29  thf('68', plain,
% 29.04/29.29      (![X1 : $i, X2 : $i, X5 : $i]:
% 29.04/29.29         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 29.04/29.29          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 29.04/29.29          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 29.04/29.29      inference('cnf', [status(esa)], [d5_xboole_0])).
% 29.04/29.29  thf('69', plain,
% 29.04/29.29      ((~ (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_B_1)
% 29.04/29.29        | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 29.04/29.29        | ((sk_B_1) = (k4_xboole_0 @ sk_A @ k1_xboole_0)))),
% 29.04/29.29      inference('sup-', [status(thm)], ['67', '68'])).
% 29.04/29.29  thf('70', plain,
% 29.04/29.29      ((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ sk_B_1)),
% 29.04/29.29      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 29.04/29.29  thf('71', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 29.04/29.29      inference('sup-', [status(thm)], ['28', '37'])).
% 29.04/29.29  thf('72', plain,
% 29.04/29.29      (((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 29.04/29.29        | ((sk_B_1) = (sk_A)))),
% 29.04/29.29      inference('demod', [status(thm)], ['69', '70', '71'])).
% 29.04/29.29  thf('73', plain, (((sk_A) != (sk_B_1))),
% 29.04/29.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.29  thf('74', plain,
% 29.04/29.29      ((r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)),
% 29.04/29.29      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 29.04/29.29  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 29.04/29.29      inference('condensation', [status(thm)], ['36'])).
% 29.04/29.29  thf('76', plain, ($false), inference('sup-', [status(thm)], ['74', '75'])).
% 29.04/29.29  
% 29.04/29.29  % SZS output end Refutation
% 29.04/29.29  
% 29.04/29.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
