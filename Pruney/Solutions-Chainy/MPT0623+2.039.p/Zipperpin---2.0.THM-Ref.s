%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qehQSpb9PT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 135 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   20
%              Number of atoms          :  724 (1224 expanded)
%              Number of equality atoms :  105 ( 186 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
        = X26 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X20 @ X17 ) @ ( sk_C_3 @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_3 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('26',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

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

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ sk_B_1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('42',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('44',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40','41','42','43'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('57',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('66',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('67',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('68',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qehQSpb9PT
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 81 iterations in 0.041s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(np__1_type, type, np__1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(t15_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ?[C:$i]:
% 0.20/0.47           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.47             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.47             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i]:
% 0.20/0.47         (((k1_relat_1 @ (sk_C_4 @ X25 @ X26)) = (X26))
% 0.20/0.47          | ((X26) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i]:
% 0.20/0.47         ((v1_funct_1 @ (sk_C_4 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.47  thf(d5_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X17 : $i, X20 : $i]:
% 0.20/0.47         (((X20) = (k2_relat_1 @ X17))
% 0.20/0.47          | (r2_hidden @ 
% 0.20/0.47             (k4_tarski @ (sk_D @ X20 @ X17) @ (sk_C_3 @ X20 @ X17)) @ X17)
% 0.20/0.47          | (r2_hidden @ (sk_C_3 @ X20 @ X17) @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.47  thf('3', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.47  thf(d1_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (((X11) != (X10))
% 0.20/0.47          | (r2_hidden @ X11 @ X12)
% 0.20/0.47          | ((X12) != (k1_tarski @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('5', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.20/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.47  thf(t3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.47          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.47  thf(t60_relat_1, axiom,
% 0.20/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.47          | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X13 @ X12)
% 0.20/0.47          | ((X13) = (X10))
% 0.20/0.47          | ((X12) != (k1_tarski @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X10 : $i, X13 : $i]:
% 0.20/0.47         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.47          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) = (k1_xboole_0))
% 0.20/0.47          | (r1_tarski @ (k1_tarski @ (sk_C_3 @ X0 @ k1_xboole_0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i]:
% 0.20/0.47         (((k2_relat_1 @ (sk_C_4 @ X25 @ X26)) = (k1_tarski @ X25))
% 0.20/0.47          | ((X26) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.47  thf(t18_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.47          ( ![C:$i]:
% 0.20/0.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.47                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.47             ( ![C:$i]:
% 0.20/0.47               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.47                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X27 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.47          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.47          | ~ (v1_funct_1 @ X27)
% 0.20/0.47          | ~ (v1_relat_1 @ X27))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.47          | ((X1) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.20/0.47          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.20/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((sk_A) = (k1_xboole_0))
% 0.20/0.47          | ((sk_B_1)
% 0.20/0.47              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.47          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.47  thf('24', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ?[B:$i]:
% 0.20/0.47       ( ( ![C:$i]:
% 0.20/0.47           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.20/0.47         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.47         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.47  thf('26', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf(t65_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X22 : $i]:
% 0.20/0.47         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.47           | ~ (v1_relat_1 @ X0)
% 0.20/0.47           | ((k2_relat_1 @ X0) = (k1_xboole_0))))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.47           | ~ (v1_relat_1 @ X0)
% 0.20/0.47           | ((k2_relat_1 @ X0) = (sk_B_1))))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((X0) != (sk_B_1))
% 0.20/0.47           | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))
% 0.20/0.47           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.47  thf('33', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((X0) != (sk_B_1)) | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X27 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.47          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.47          | ~ (v1_funct_1 @ X27)
% 0.20/0.47          | ~ (v1_relat_1 @ X27))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.47         | ~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.20/0.47         | ~ (v1_funct_1 @ (sk_B @ sk_B_1))
% 0.20/0.47         | ((sk_B_1) != (k1_relat_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('39', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('42', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('43', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['37', '40', '41', '42', '43'])).
% 0.20/0.47  thf('45', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.47      inference('split', [status(esa)], ['24'])).
% 0.20/0.47  thf('47', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.20/0.47  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['25', '47'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((sk_B_1)
% 0.20/0.47            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.47          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['23', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) = (k1_xboole_0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ((sk_B_1)
% 0.20/0.47              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((sk_B_1)
% 0.20/0.47            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i]:
% 0.20/0.47         ((v1_relat_1 @ (sk_C_4 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) = (k1_xboole_0))
% 0.20/0.47          | ((sk_B_1)
% 0.20/0.47              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.20/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '53'])).
% 0.20/0.47  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.47  thf('56', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      (![X22 : $i]:
% 0.20/0.47         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.47          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.47  thf('59', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) != (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.47  thf('61', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (![X27 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.47          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.47          | ~ (v1_funct_1 @ X27)
% 0.20/0.47          | ~ (v1_relat_1 @ X27))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.47        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.47        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.47  thf('64', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('65', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('66', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('67', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.47  thf('68', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.20/0.47  thf('69', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['55', '68'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
