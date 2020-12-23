%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p5FqB3X7tY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 (1298 expanded)
%              Number of leaves         :   25 ( 378 expanded)
%              Depth                    :   27
%              Number of atoms          :  935 (12816 expanded)
%              Number of equality atoms :  131 (1867 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X30 @ X31 ) )
        = X31 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X30 @ X31 ) )
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

thf('15',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
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
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X26 ) )
      = X26 ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
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
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
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
    ! [X26: $i] :
      ( v1_funct_1 @ ( sk_B @ X26 ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_A @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_A @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ sk_A ) )
      | ( ( sk_D @ k1_xboole_0 @ sk_A @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ sk_A ) )
      | ( ( sk_D @ k1_xboole_0 @ sk_A @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ sk_A ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ sk_A ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(condensation,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['46','60'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('72',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('76',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('78',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73','78'])).

thf('80',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','36'])).

thf('83',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('86',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('87',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['61','91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X0 )
      | ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['61','91'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['61','91'])).

thf('97',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(condensation,[status(thm)],['59'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','90'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p5FqB3X7tY
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 158 iterations in 0.062s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(d4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.20/0.51         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.51          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['0'])).
% 0.20/0.51  thf(t15_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ?[C:$i]:
% 0.20/0.51           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.51             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.51             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (sk_C_3 @ X30 @ X31)) = (X31))
% 0.20/0.51          | ((X31) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (sk_C_3 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (sk_C_3 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.51          | ((X17) = (X14))
% 0.20/0.51          | ((X16) != (k1_tarski @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X14 : $i, X17 : $i]:
% 0.20/0.51         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X0 @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (sk_C_3 @ X30 @ X31)) = (k1_tarski @ X30))
% 0.20/0.51          | ((X31) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf(t18_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.51                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.51                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X32 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.51          | ~ (v1_funct_1 @ X32)
% 0.20/0.51          | ~ (v1_relat_1 @ X32))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X0)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.51          | ((X1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X1)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ sk_A @ X1)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_B_1) != (X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf(t60_relat_1, axiom,
% 0.20/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X32 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.51          | ~ (v1_funct_1 @ X32)
% 0.20/0.51          | ~ (v1_relat_1 @ X32))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('27', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51        | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ?[B:$i]:
% 0.20/0.51       ( ( ![C:$i]:
% 0.20/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.51  thf('30', plain, (![X26 : $i]: ((k1_relat_1 @ (sk_B @ X26)) = (X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf(t64_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X21 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.20/0.51          | ((X21) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) != (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.51          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf('36', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '37'])).
% 0.20/0.51  thf('39', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.51  thf('40', plain, (![X26 : $i]: (v1_funct_1 @ (sk_B @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('41', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '41'])).
% 0.20/0.51  thf('43', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['23', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.20/0.51         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X1)
% 0.20/0.51          | ((X1) = (k3_xboole_0 @ X0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ sk_A @ X0) @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X0 @ sk_A @ X1) @ X0)
% 0.20/0.51          | ((X0) = (k3_xboole_0 @ X1 @ sk_A)))),
% 0.20/0.51      inference('condensation', [status(thm)], ['49'])).
% 0.20/0.51  thf('51', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_A @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X14 : $i, X17 : $i]:
% 0.20/0.51         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ sk_A))
% 0.20/0.51          | ((sk_D @ k1_xboole_0 @ sk_A @ X1) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ sk_A))
% 0.20/0.51          | ((sk_D @ k1_xboole_0 @ sk_A @ X1) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X1))
% 0.20/0.51          | ((k1_xboole_0) = (k3_xboole_0 @ X2 @ sk_A))
% 0.20/0.51          | ((k1_xboole_0) = (k3_xboole_0 @ X2 @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (k3_xboole_0 @ X2 @ sk_A)) | ((X0) = (X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.51  thf('60', plain, (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ sk_A))),
% 0.20/0.51      inference('condensation', [status(thm)], ['59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_A) = (k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1))),
% 0.20/0.51      inference('demod', [status(thm)], ['46', '60'])).
% 0.20/0.51  thf('62', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X32 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.51          | ~ (v1_funct_1 @ X32)
% 0.20/0.51          | ~ (v1_relat_1 @ X32))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.51         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('72', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '73', '78'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('83', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['81', '82'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['80', '83'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('86', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('87', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['84', '87'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['62'])).
% 0.20/0.51  thf('90', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['63', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['61', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.20/0.51         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X0)
% 0.20/0.51          | ((sk_A) = (k3_xboole_0 @ X0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['61', '91'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ X1)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['61', '91'])).
% 0.20/0.51  thf('97', plain, (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ sk_A))),
% 0.20/0.51      inference('condensation', [status(thm)], ['59'])).
% 0.20/0.51  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.20/0.51  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['63', '90'])).
% 0.20/0.51  thf('100', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
