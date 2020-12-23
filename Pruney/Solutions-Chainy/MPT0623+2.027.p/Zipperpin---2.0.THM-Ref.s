%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1oRe9XyN3a

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 138 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  694 (1262 expanded)
%              Number of equality atoms :   96 ( 190 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_5 @ X30 @ X31 ) )
        = X31 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( sk_C_5 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ X20 @ X17 ) @ ( sk_D @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_3 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
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
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_5 @ X30 @ X31 ) )
        = ( k1_tarski @ X30 ) )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_5 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
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

thf('27',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
        = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('36',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ sk_B_1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('43',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('44',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','41','42','43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_relat_1 @ ( sk_C_5 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('58',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('59',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('64',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('65',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('66',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1oRe9XyN3a
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 97 iterations in 0.048s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_C_5_type, type, sk_C_5: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(t15_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ?[C:$i]:
% 0.21/0.53           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.53             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.53             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         (((k1_relat_1 @ (sk_C_5 @ X30 @ X31)) = (X31))
% 0.21/0.53          | ((X31) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         ((v1_funct_1 @ (sk_C_5 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.53  thf(d4_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X17 : $i, X20 : $i]:
% 0.21/0.53         (((X20) = (k1_relat_1 @ X17))
% 0.21/0.53          | (r2_hidden @ 
% 0.21/0.53             (k4_tarski @ (sk_C_3 @ X20 @ X17) @ (sk_D @ X20 @ X17)) @ X17)
% 0.21/0.53          | (r2_hidden @ (sk_C_3 @ X20 @ X17) @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('3', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         (((X11) != (X10))
% 0.21/0.53          | (r2_hidden @ X11 @ X12)
% 0.21/0.53          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('5', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.21/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.53  thf(t3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.53          | ~ (r2_hidden @ X6 @ X7)
% 0.21/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.53          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.53  thf(t60_relat_1, axiom,
% 0.21/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.53          | ((X13) = (X10))
% 0.21/0.53          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X10 : $i, X13 : $i]:
% 0.21/0.53         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ (sk_C_3 @ X0 @ k1_xboole_0)) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         (((k2_relat_1 @ (sk_C_5 @ X30 @ X31)) = (k1_tarski @ X30))
% 0.21/0.53          | ((X31) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.53  thf(t18_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53          ( ![C:$i]:
% 0.21/0.53            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.53              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.53                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.53                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.53                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X32 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.21/0.53          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.21/0.53          | ~ (v1_funct_1 @ X32)
% 0.21/0.53          | ~ (v1_relat_1 @ X32))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.53          | ((X1) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_5 @ X0 @ X1))
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_C_5 @ X0 @ X1))
% 0.21/0.53          | ((sk_B_1) != (k1_relat_1 @ (sk_C_5 @ X0 @ X1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_A) = (k1_xboole_0))
% 0.21/0.53          | ((sk_B_1)
% 0.21/0.53              != (k1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.53  thf('24', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ?[B:$i]:
% 0.21/0.53       ( ( ![C:$i]:
% 0.21/0.53           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.53             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.53         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.53  thf('27', plain, (![X26 : $i]: ((k1_relat_1 @ (sk_B @ X26)) = (X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf(t65_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X22 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.21/0.53          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) != (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.53          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.53        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.21/0.53         | ((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.21/0.53         | ((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.53  thf('35', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X32 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.21/0.53          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.21/0.53          | ~ (v1_funct_1 @ X32)
% 0.21/0.53          | ~ (v1_relat_1 @ X32))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.53         | ~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.21/0.53         | ~ (v1_funct_1 @ (sk_B @ sk_B_1))
% 0.21/0.53         | ((sk_B_1) != (k1_relat_1 @ (sk_B @ sk_B_1)))))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('40', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('43', plain, (![X26 : $i]: (v1_funct_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('44', plain, (![X26 : $i]: ((k1_relat_1 @ (sk_B @ X26)) = (X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '41', '42', '43', '44'])).
% 0.21/0.53  thf('46', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['24'])).
% 0.21/0.53  thf('48', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['25', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B_1)
% 0.21/0.53            != (k1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.53          | ~ (v1_funct_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ((sk_B_1)
% 0.21/0.53              != (k1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B_1)
% 0.21/0.53            != (k1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.21/0.53          | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X30 : $i, X31 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (sk_C_5 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | ((sk_B_1)
% 0.21/0.53              != (k1_relat_1 @ (sk_C_5 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.21/0.53      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '54'])).
% 0.21/0.53  thf('56', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 0.21/0.53        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  thf('58', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('59', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X32 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.21/0.53          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.21/0.53          | ~ (v1_funct_1 @ X32)
% 0.21/0.53          | ~ (v1_relat_1 @ X32))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.53        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.53        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.53        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('63', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('64', plain, (![X26 : $i]: (v1_funct_1 @ (sk_B @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('65', plain, (![X26 : $i]: ((k1_relat_1 @ (sk_B @ X26)) = (X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.53  thf('66', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.21/0.53  thf('67', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['56', '66'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
