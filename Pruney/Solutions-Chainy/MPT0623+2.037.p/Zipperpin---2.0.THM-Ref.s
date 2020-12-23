%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDn2ienRPo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 493 expanded)
%              Number of leaves         :   26 ( 144 expanded)
%              Depth                    :   21
%              Number of atoms          :  915 (4802 expanded)
%              Number of equality atoms :  141 ( 829 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X12 ) @ ( sk_C_2 @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
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
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
        = X21 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
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
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

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

thf('40',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('50',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('51',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','55'])).

thf('57',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('60',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('67',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','73'])).

thf('75',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('77',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('78',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('87',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','87'])).

thf('89',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('90',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('91',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['56','95'])).

thf('97',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','94'])).

thf('102',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(simplify,[status(thm)],['102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDn2ienRPo
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:32:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 138 iterations in 0.132s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.40/0.59  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.40/0.59  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(t60_relat_1, axiom,
% 0.40/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('0', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf(d5_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X12 : $i, X15 : $i]:
% 0.40/0.59         (((X15) = (k2_relat_1 @ X12))
% 0.40/0.59          | (r2_hidden @ 
% 0.40/0.59             (k4_tarski @ (sk_D @ X15 @ X12) @ (sk_C_2 @ X15 @ X12)) @ X12)
% 0.40/0.59          | (r2_hidden @ (sk_C_2 @ X15 @ X12) @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.40/0.59          | (r2_hidden @ X11 @ X13)
% 0.40/0.59          | ((X13) != (k2_relat_1 @ X12)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.40/0.59          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.40/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.40/0.59          | ((X1) = (k2_relat_1 @ X0))
% 0.40/0.59          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '3'])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.59          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.40/0.59          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['0', '4'])).
% 0.40/0.59  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.59  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf(d3_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.59          | (r2_hidden @ X0 @ X2)
% 0.40/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.40/0.59          | ((X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('clc', [status(thm)], ['7', '10'])).
% 0.40/0.59  thf(t15_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ?[C:$i]:
% 0.40/0.59           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.40/0.59             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.59             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         (((k1_relat_1 @ (sk_C_3 @ X20 @ X21)) = (X21))
% 0.40/0.59          | ((X21) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         ((v1_relat_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         ((v1_funct_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X1 : $i, X3 : $i]:
% 0.40/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X1 : $i, X3 : $i]:
% 0.40/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf(d1_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X5 : $i, X8 : $i]:
% 0.40/0.59         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['16', '18'])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X1 : $i, X3 : $i]:
% 0.40/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.59          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.59          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ X0 @ X1)
% 0.40/0.59          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i]:
% 0.40/0.59         (((k2_relat_1 @ (sk_C_3 @ X20 @ X21)) = (k1_tarski @ X20))
% 0.40/0.59          | ((X21) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.59  thf(t18_funct_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.59          ( ![C:$i]:
% 0.40/0.59            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.59              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.59                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.59             ( ![C:$i]:
% 0.40/0.59               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.59                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.59                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X22 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.40/0.59          | ~ (v1_funct_1 @ X22)
% 0.40/0.59          | ~ (v1_relat_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.40/0.59          | ((X1) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.40/0.59          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ sk_A @ X0)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.40/0.59          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.59          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.59          | ((X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.59          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ sk_A @ X1)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.59          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.59          | ((X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.59          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['13', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ sk_A @ X1)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.59          | ((X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((sk_B_1) != (X0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | ((X0) = (k1_xboole_0))
% 0.40/0.59          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.59  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X22 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.40/0.59          | ~ (v1_funct_1 @ X22)
% 0.40/0.59          | ~ (v1_relat_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.40/0.59        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.59        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.59  thf('37', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.59        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.59        | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.40/0.59  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ?[B:$i]:
% 0.40/0.59       ( ( ![C:$i]:
% 0.40/0.59           ( ( r2_hidden @ C @ A ) =>
% 0.40/0.59             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.59         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.40/0.59         ( v1_relat_1 @ B ) ) ))).
% 0.40/0.59  thf('40', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf(t64_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X17 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.40/0.59          | ((X17) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((X0) != (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.40/0.59          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf('45', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.59  thf('46', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['39', '47'])).
% 0.40/0.59  thf('49', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.59  thf('50', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('51', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.40/0.59      inference('sup+', [status(thm)], ['49', '50'])).
% 0.40/0.59  thf('52', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['48', '51'])).
% 0.40/0.59  thf('53', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['33', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.59          | (r2_hidden @ X0 @ X2)
% 0.40/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((sk_A) = (k1_xboole_0))
% 0.40/0.59          | (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['11', '55'])).
% 0.40/0.59  thf('57', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('60', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X22 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.40/0.59          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.40/0.59          | ~ (v1_funct_1 @ X22)
% 0.40/0.59          | ~ (v1_relat_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.40/0.59         | ~ (v1_relat_1 @ sk_B_1)
% 0.40/0.59         | ~ (v1_funct_1 @ sk_B_1)
% 0.40/0.59         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('67', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['66', '67'])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('71', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['69', '70'])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (((~ (v1_relat_1 @ sk_B_1)
% 0.40/0.59         | ~ (v1_funct_1 @ sk_B_1)
% 0.40/0.59         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '68', '73'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.40/0.59  thf('76', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (![X17 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.40/0.59          | ((X17) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      ((![X0 : $i]:
% 0.40/0.59          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.40/0.59           | ~ (v1_relat_1 @ X0)
% 0.40/0.59           | ((X0) = (k1_xboole_0))))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      ((![X0 : $i]:
% 0.40/0.59          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.40/0.59           | ~ (v1_relat_1 @ X0)
% 0.40/0.59           | ((X0) = (sk_B_1))))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['79', '80'])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      ((![X0 : $i]:
% 0.40/0.59          (((X0) != (sk_B_1))
% 0.40/0.59           | ((sk_B @ X0) = (sk_B_1))
% 0.40/0.59           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['76', '81'])).
% 0.40/0.59  thf('83', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.40/0.59         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['84'])).
% 0.40/0.59  thf('86', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('87', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['85', '86'])).
% 0.40/0.59  thf('88', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['75', '87'])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['84'])).
% 0.40/0.59  thf('90', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.59  thf('91', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['89', '90'])).
% 0.40/0.59  thf('92', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['88', '91'])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.59      inference('split', [status(esa)], ['57'])).
% 0.40/0.59  thf('94', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.40/0.59  thf('95', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['58', '94'])).
% 0.40/0.59  thf('96', plain,
% 0.40/0.59      (![X0 : $i]: (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['56', '95'])).
% 0.40/0.59  thf('97', plain,
% 0.40/0.59      (![X5 : $i, X8 : $i]:
% 0.40/0.59         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.59  thf('98', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['96', '97'])).
% 0.40/0.59  thf('99', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['96', '97'])).
% 0.40/0.59  thf('100', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.40/0.59      inference('sup+', [status(thm)], ['98', '99'])).
% 0.40/0.59  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['58', '94'])).
% 0.40/0.59  thf('102', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['100', '101'])).
% 0.40/0.59  thf('103', plain, ($false), inference('simplify', [status(thm)], ['102'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
