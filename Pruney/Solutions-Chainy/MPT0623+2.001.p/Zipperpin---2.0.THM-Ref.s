%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HGw7RpNExK

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 392 expanded)
%              Number of leaves         :   26 ( 117 expanded)
%              Depth                    :   21
%              Number of atoms          :  800 (3468 expanded)
%              Number of equality atoms :  110 ( 555 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['7','10'])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
        = X22 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('25',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('34',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','50'])).

thf('52',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('64',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','70'])).

thf('72',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['51','83'])).

thf('85',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','82'])).

thf('90',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HGw7RpNExK
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 119 iterations in 0.070s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.52  thf(t60_relat_1, axiom,
% 0.20/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf(d4_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X13 : $i, X16 : $i]:
% 0.20/0.52         (((X16) = (k1_relat_1 @ X13))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C_2 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 0.20/0.52          | (r2_hidden @ (sk_C_2 @ X16 @ X13) @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 0.20/0.52          | (r2_hidden @ X11 @ X14)
% 0.20/0.52          | ((X14) != (k1_relat_1 @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         ((r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.20/0.52          | ((X1) = (k1_relat_1 @ X0))
% 0.20/0.52          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.52  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.20/0.52          | ((X0) = (k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.52          | ((X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['7', '10'])).
% 0.20/0.52  thf(t15_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ?[C:$i]:
% 0.20/0.52           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.52             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (sk_C_3 @ X21 @ X22)) = (X22))
% 0.20/0.52          | ((X22) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         ((v1_funct_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(d1_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X5 : $i, X8 : $i]:
% 0.20/0.52         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (sk_C_3 @ X21 @ X22)) = (k1_tarski @ X21))
% 0.20/0.52          | ((X22) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.52  thf(t18_funct_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.52                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.52                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X23 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.20/0.52          | ((sk_B) != (k1_relat_1 @ X23))
% 0.20/0.52          | ~ (v1_funct_1 @ X23)
% 0.20/0.52          | ~ (v1_relat_1 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.52          | ((X1) = (k1_xboole_0))
% 0.20/0.52          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.52          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_A @ X0)
% 0.20/0.52          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.20/0.52          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.53          | ((X1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.53          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_A @ X1)
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.53          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_A @ X1)
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.53          | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((sk_B) != (X0))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf(cc1_funct_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.20/0.53  thf('34', plain, (![X18 : $i]: ((v1_funct_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.20/0.53  thf(cc1_relat_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.53  thf('35', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.53  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X23 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ X23))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) != (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) != (k1_xboole_0))
% 0.20/0.53        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '41'])).
% 0.20/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.53  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((sk_B) != (k1_xboole_0)) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) != (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '44'])).
% 0.20/0.53  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['33', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_A) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '50'])).
% 0.20/0.53  thf('52', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('54', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.53  thf('55', plain, (![X18 : $i]: ((v1_funct_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X23 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.20/0.53          | ((sk_B) != (k1_relat_1 @ X23))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((~ (r1_tarski @ sk_B @ sk_A)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('64', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ((sk_B) != (sk_B))))
% 0.20/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '65', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (((~ (v1_funct_1 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf('76', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ((~ (v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['73', '76'])).
% 0.20/0.53  thf('78', plain, ((~ (v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '77'])).
% 0.20/0.53  thf('79', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('80', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['52'])).
% 0.20/0.53  thf('82', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['53', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]: (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['51', '83'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (![X5 : $i, X8 : $i]:
% 0.20/0.53         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('86', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('88', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['53', '82'])).
% 0.20/0.53  thf('90', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
