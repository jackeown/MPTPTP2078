%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jm0SDmr7p2

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 338 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   25
%              Number of atoms          : 1005 (3191 expanded)
%              Number of equality atoms :  145 ( 476 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

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

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X24 @ X25 ) )
        = X25 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X24 @ X25 ) )
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

thf('15',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

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

thf('30',plain,(
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

thf('31',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','37'])).

thf('39',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf('40',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('41',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( ( sk_C_1 @ X1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( ( sk_C_1 @ X1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ sk_A @ X2 )
      | ( r1_xboole_0 @ sk_A @ X2 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ sk_A @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( r1_xboole_0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('65',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','69'])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('81',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('84',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('85',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82','87'])).

thf('89',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('91',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('101',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','101'])).

thf('103',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('104',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('105',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('108',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['72','108'])).

thf('110',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jm0SDmr7p2
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 325 iterations in 0.188s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(t2_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf(t3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf(t15_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ?[C:$i]:
% 0.45/0.65           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.45/0.65             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.45/0.65             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         (((k1_relat_1 @ (sk_C_3 @ X24 @ X25)) = (X25))
% 0.45/0.65          | ((X25) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((v1_relat_1 @ (sk_C_3 @ X24 @ X25)) | ((X25) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((v1_funct_1 @ (sk_C_3 @ X24 @ X25)) | ((X25) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.65  thf(d3_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X1 : $i, X3 : $i]:
% 0.45/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X1 : $i, X3 : $i]:
% 0.45/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf(d1_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X19 @ X18)
% 0.45/0.65          | ((X19) = (X16))
% 0.45/0.65          | ((X18) != (k1_tarski @ X16)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X16 : $i, X19 : $i]:
% 0.45/0.65         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X1 : $i, X3 : $i]:
% 0.45/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ X0 @ X1)
% 0.45/0.65          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         (((k2_relat_1 @ (sk_C_3 @ X24 @ X25)) = (k1_tarski @ X24))
% 0.45/0.65          | ((X25) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.65  thf(t18_funct_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65          ( ![C:$i]:
% 0.45/0.65            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.65              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.45/0.65                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65             ( ![C:$i]:
% 0.45/0.65               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.65                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.45/0.65                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X26 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k2_relat_1 @ X26) @ sk_A)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ X26))
% 0.45/0.65          | ~ (v1_funct_1 @ X26)
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.45/0.65          | ((X1) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.65          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ sk_A @ X0)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.45/0.65          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.45/0.65          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.45/0.65          | ((X1) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.65          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ sk_A @ X1)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.45/0.65          | ((X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.65          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ sk_A @ X1)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.65          | ((X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((sk_B_1) != (X0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf(t60_relat_1, axiom,
% 0.45/0.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X26 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k2_relat_1 @ X26) @ sk_A)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ X26))
% 0.45/0.65          | ~ (v1_funct_1 @ X26)
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.45/0.65        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.65        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.65  thf('27', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.65        | ((sk_B_1) != (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.45/0.65  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ?[B:$i]:
% 0.45/0.65       ( ( ![C:$i]:
% 0.45/0.65           ( ( r2_hidden @ C @ A ) =>
% 0.45/0.65             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.45/0.65         ( v1_relat_1 @ B ) ) ))).
% 0.45/0.65  thf('30', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B @ X22)) = (X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf(t64_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X21 : $i]:
% 0.45/0.65         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.45/0.65          | ((X21) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X21))),
% 0.45/0.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((X0) != (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.45/0.65          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('33', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.65  thf('36', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '37'])).
% 0.45/0.65  thf('39', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.65  thf('40', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('41', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.45/0.65      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['38', '41'])).
% 0.45/0.65  thf('43', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['23', '42'])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.65          | (r2_hidden @ X0 @ X2)
% 0.45/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X16 : $i, X19 : $i]:
% 0.45/0.65         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ sk_A @ X1) | ((sk_C_1 @ X1 @ sk_A) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ sk_A @ X1) | ((sk_C_1 @ X1 @ sk_A) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (X1)) | (r1_xboole_0 @ sk_A @ X2) | (r1_xboole_0 @ sk_A @ X2))),
% 0.45/0.65      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ sk_A @ X2) | ((X0) = (X1)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['50'])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X12 @ X10)
% 0.45/0.65          | ~ (r2_hidden @ X12 @ X13)
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.65          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.45/0.65          | (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['52', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (((X1) = (X2)) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['51', '57'])).
% 0.45/0.65  thf('59', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['38', '41'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (((sk_B_1) != (X0)) | (r1_xboole_0 @ X1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.65  thf('61', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ sk_A)),
% 0.45/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.65  thf(d4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.45/0.65         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.65          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.65          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['62'])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X12 @ X10)
% 0.45/0.65          | ~ (r2_hidden @ X12 @ X13)
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.65          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 0.45/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.45/0.65          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.45/0.65          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.65  thf('69', plain, (![X0 : $i]: ((sk_A) = (k3_xboole_0 @ sk_A @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['61', '68'])).
% 0.45/0.65  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '69'])).
% 0.45/0.65  thf('71', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('74', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X26 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k2_relat_1 @ X26) @ sk_A)
% 0.45/0.65          | ((sk_B_1) != (k1_relat_1 @ X26))
% 0.45/0.65          | ~ (v1_funct_1 @ X26)
% 0.45/0.65          | ~ (v1_relat_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.45/0.65         | ~ (v1_relat_1 @ sk_B_1)
% 0.45/0.65         | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.65         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('81', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['80', '81'])).
% 0.45/0.65  thf('83', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('84', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['83', '84'])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('87', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['85', '86'])).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (((~ (v1_relat_1 @ sk_B_1)
% 0.45/0.65         | ~ (v1_funct_1 @ sk_B_1)
% 0.45/0.65         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['79', '82', '87'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.45/0.65  thf('90', plain, (![X22 : $i]: ((k1_relat_1 @ (sk_B @ X22)) = (X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('91', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (![X21 : $i]:
% 0.45/0.65         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.45/0.65          | ((X21) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X21))),
% 0.45/0.65      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.65  thf('93', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.45/0.65           | ~ (v1_relat_1 @ X0)
% 0.45/0.65           | ((X0) = (k1_xboole_0))))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.65  thf('94', plain,
% 0.45/0.65      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.45/0.65           | ~ (v1_relat_1 @ X0)
% 0.45/0.65           | ((X0) = (sk_B_1))))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.65  thf('96', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (((X0) != (sk_B_1))
% 0.45/0.65           | ((sk_B @ X0) = (sk_B_1))
% 0.45/0.65           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['90', '95'])).
% 0.45/0.65  thf('97', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('98', plain,
% 0.45/0.65      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.45/0.65         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['96', '97'])).
% 0.45/0.65  thf('99', plain,
% 0.45/0.65      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['98'])).
% 0.45/0.65  thf('100', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['99', '100'])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['89', '101'])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['98'])).
% 0.45/0.65  thf('104', plain, (![X22 : $i]: (v1_funct_1 @ (sk_B @ X22))),
% 0.45/0.65      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.45/0.65  thf('105', plain,
% 0.45/0.65      (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['103', '104'])).
% 0.45/0.65  thf('106', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['102', '105'])).
% 0.45/0.65  thf('107', plain,
% 0.45/0.65      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['71'])).
% 0.45/0.65  thf('108', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.45/0.65  thf('109', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['72', '108'])).
% 0.45/0.65  thf('110', plain, ($false),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['70', '109'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
