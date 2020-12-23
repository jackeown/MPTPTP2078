%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWnAF4qnfv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 176 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  628 (1469 expanded)
%              Number of equality atoms :   86 ( 208 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

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

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X24 @ X25 ) )
        = X25 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19
        = ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X19 @ X16 ) @ ( sk_C_3 @ X19 @ X16 ) ) @ X16 )
      | ( r2_hidden @ ( sk_C_3 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_3 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X24 @ X25 ) )
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 ) ) ),
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

thf('21',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('28',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('41',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('42',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('43',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','48'])).

thf('50',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','47'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWnAF4qnfv
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 96 iterations in 0.039s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.49  thf(t15_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ?[C:$i]:
% 0.21/0.49           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.49             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         (((k1_relat_1 @ (sk_C_4 @ X24 @ X25)) = (X25))
% 0.21/0.49          | ((X25) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (sk_C_4 @ X24 @ X25)) | ((X25) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.49  thf(d5_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X16 : $i, X19 : $i]:
% 0.21/0.49         (((X19) = (k2_relat_1 @ X16))
% 0.21/0.49          | (r2_hidden @ 
% 0.21/0.49             (k4_tarski @ (sk_D @ X19 @ X16) @ (sk_C_3 @ X19 @ X16)) @ X16)
% 0.21/0.49          | (r2_hidden @ (sk_C_3 @ X19 @ X16) @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.49  thf('3', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (((X10) != (X9))
% 0.21/0.49          | (r2_hidden @ X10 @ X11)
% 0.21/0.49          | ((X11) != (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('5', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf(t3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.49          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.49          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.49          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf(t60_relat_1, axiom,
% 0.21/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X12 @ X11)
% 0.21/0.49          | ((X12) = (X9))
% 0.21/0.49          | ((X11) != (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X9 : $i, X12 : $i]:
% 0.21/0.49         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.49          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.49          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) = (k1_xboole_0))
% 0.21/0.49          | (r1_tarski @ (k1_tarski @ (sk_C_3 @ X0 @ k1_xboole_0)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (sk_C_4 @ X24 @ X25)) = (k1_tarski @ X24))
% 0.21/0.49          | ((X25) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.49  thf(t18_funct_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.49                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.49             ( ![C:$i]:
% 0.21/0.49               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.49                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X26) @ sk_A)
% 0.21/0.49          | ((sk_B_1) != (k1_relat_1 @ X26))
% 0.21/0.49          | ~ (v1_funct_1 @ X26)
% 0.21/0.49          | ~ (v1_relat_1 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.49          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.49          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_A) = (k1_xboole_0))
% 0.21/0.49          | ((sk_B_1)
% 0.21/0.49              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.49          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('24', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['24'])).
% 0.21/0.49  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X26) @ sk_A)
% 0.21/0.49          | ((sk_B_1) != (k1_relat_1 @ X26))
% 0.21/0.49          | ~ (v1_funct_1 @ X26)
% 0.21/0.49          | ~ (v1_relat_1 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49        | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ?[B:$i]:
% 0.21/0.49       ( ( ![C:$i]:
% 0.21/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.49  thf('32', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B @ X22)) = (X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf(t64_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X21 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.21/0.49          | ((X21) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.49          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49        | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '39'])).
% 0.21/0.49  thf('41', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('42', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('43', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.49  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '48'])).
% 0.21/0.49  thf('50', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.49      inference('split', [status(esa)], ['24'])).
% 0.21/0.49  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['25', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B_1)
% 0.21/0.49            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.49          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['23', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ((sk_B_1)
% 0.21/0.49              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B_1)
% 0.21/0.49            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (sk_C_4 @ X24 @ X25)) | ((X25) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) = (k1_xboole_0))
% 0.21/0.49          | ((sk_B_1)
% 0.21/0.49              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.21/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '58'])).
% 0.21/0.49  thf('60', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.49  thf('61', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.49  thf('62', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
