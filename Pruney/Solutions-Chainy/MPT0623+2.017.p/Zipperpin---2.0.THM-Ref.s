%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjlxfFH36h

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 184 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  764 (1713 expanded)
%              Number of equality atoms :  129 ( 299 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
        = X17 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 ) ) ),
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

thf('13',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

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

thf('28',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','35'])).

thf('37',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('38',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','40'])).

thf('42',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('49',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('56',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','57','62'])).

thf('64',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('67',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('76',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','76'])).

thf('78',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('79',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('80',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['47','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjlxfFH36h
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 62 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(t15_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ?[C:$i]:
% 0.21/0.48           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.48             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.48             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))
% 0.21/0.48          | ((X17) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (sk_C_2 @ X16 @ X17)) | ((X17) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         ((v1_funct_1 @ (sk_C_2 @ X16 @ X17)) | ((X17) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.48          | ((X11) = (X8))
% 0.21/0.48          | ((X10) != (k1_tarski @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X8 : $i, X11 : $i]:
% 0.21/0.48         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.48          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ X0 @ X1)
% 0.21/0.48          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (sk_C_2 @ X16 @ X17)) = (k1_tarski @ X16))
% 0.21/0.48          | ((X17) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.48  thf(t18_funct_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.48          ( ![C:$i]:
% 0.21/0.48            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.48                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.48             ( ![C:$i]:
% 0.21/0.48               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.48                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X18 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ X18))
% 0.21/0.48          | ~ (v1_funct_1 @ X18)
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_A @ X0)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.21/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.48          | ((X1) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.48          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_A @ X1)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.48          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_A @ X1)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((sk_B_1) != (X0))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X18 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ X18))
% 0.21/0.48          | ~ (v1_funct_1 @ X18)
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.48        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('25', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('26', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.48        | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ?[B:$i]:
% 0.21/0.48       ( ( ![C:$i]:
% 0.21/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.48  thf('28', plain, (![X14 : $i]: ((k1_relat_1 @ (sk_B @ X14)) = (X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf(t64_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.21/0.48          | ((X13) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) != (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.48          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('34', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '35'])).
% 0.21/0.48  thf('37', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('38', plain, (![X14 : $i]: (v1_funct_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '39'])).
% 0.21/0.48  thf('41', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['21', '40'])).
% 0.21/0.48  thf('42', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i]:
% 0.21/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.48  thf('46', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('49', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X18 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.21/0.48          | ((sk_B_1) != (k1_relat_1 @ X18))
% 0.21/0.48          | ~ (v1_funct_1 @ X18)
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['54', '57', '62'])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.48  thf('65', plain, (![X14 : $i]: ((k1_relat_1 @ (sk_B @ X14)) = (X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.21/0.48          | ((X13) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.21/0.48           | ~ (v1_relat_1 @ X0)
% 0.21/0.48           | ((X0) = (k1_xboole_0))))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('70', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.21/0.48           | ~ (v1_relat_1 @ X0)
% 0.21/0.48           | ((X0) = (sk_B_1))))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (((X0) != (sk_B_1))
% 0.21/0.48           | ((sk_B @ X0) = (sk_B_1))
% 0.21/0.48           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['65', '70'])).
% 0.21/0.48  thf('72', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('73', plain,
% 0.21/0.48      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.21/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.48  thf('75', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('76', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['74', '75'])).
% 0.21/0.48  thf('77', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['64', '76'])).
% 0.21/0.48  thf('78', plain,
% 0.21/0.48      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.48  thf('79', plain, (![X14 : $i]: (v1_funct_1 @ (sk_B @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.48  thf('80', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.48  thf('81', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['77', '80'])).
% 0.21/0.48  thf('82', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['46'])).
% 0.21/0.48  thf('83', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.21/0.48  thf('84', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['47', '83'])).
% 0.21/0.48  thf('85', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['45', '84'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
