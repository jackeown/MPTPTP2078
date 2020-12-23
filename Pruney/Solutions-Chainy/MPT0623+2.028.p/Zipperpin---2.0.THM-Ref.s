%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5uBuB2cyR

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 952 expanded)
%              Number of leaves         :   28 ( 294 expanded)
%              Depth                    :   32
%              Number of atoms          :  991 (9319 expanded)
%              Number of equality atoms :  148 (1341 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

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
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X23 @ X24 ) )
        = X24 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X23 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X23 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X23 @ X24 ) )
        = ( k1_tarski @ X23 ) )
      | ( X24 = k1_xboole_0 ) ) ),
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
    ! [X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
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
    ! [X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X21 ) )
      = X21 ) ),
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
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B @ X21 ) ) ),
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
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('37',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('38',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','35','38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['23','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_D @ X0 @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k1_relat_1 @ X0 ) @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ ( k1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) )
        = ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k1_relat_1 @ X0 ) @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_A ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ sk_A @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('82',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('85',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('86',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('88',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('89',plain,
    ( ( ( sk_B @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('91',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( sk_B @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('93',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('95',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','83','86','93','98'])).

thf('100',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['72'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['73','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ sk_A @ sk_A ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','103'])).

thf('105',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ sk_A )
      = X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ sk_A @ sk_A )
      = X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','35','38','39'])).

thf('110',plain,(
    ! [X0: $i] : ( sk_B_1 != X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(simplify,[status(thm)],['110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o5uBuB2cyR
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:05:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 122 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.21/0.56  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ?[C:$i]:
% 0.21/0.56       ( ( ![D:$i]:
% 0.21/0.56           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.21/0.56         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.56         ( v1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]: ((k1_relat_1 @ (sk_C_3 @ X18 @ X19)) = (X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf(d4_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X12 : $i, X15 : $i]:
% 0.21/0.56         (((X15) = (k1_relat_1 @ X12))
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k4_tarski @ (sk_C_2 @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ X15 @ X12) @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.56  thf(t15_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ?[C:$i]:
% 0.21/0.56           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.56             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.56             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (((k1_relat_1 @ (sk_C_4 @ X23 @ X24)) = (X24))
% 0.21/0.56          | ((X24) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((v1_relat_1 @ (sk_C_4 @ X23 @ X24)) | ((X24) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         ((v1_funct_1 @ (sk_C_4 @ X23 @ X24)) | ((X24) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf(d1_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X5 : $i, X8 : $i]:
% 0.21/0.56         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.56          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ X0 @ X1)
% 0.21/0.56          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (((k2_relat_1 @ (sk_C_4 @ X23 @ X24)) = (k1_tarski @ X23))
% 0.21/0.56          | ((X24) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.56  thf(t18_funct_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56          ( ![C:$i]:
% 0.21/0.56            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.56                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.56                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X25 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k2_relat_1 @ X25) @ sk_A)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ X25))
% 0.21/0.56          | ~ (v1_funct_1 @ X25)
% 0.21/0.56          | ~ (v1_relat_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.56          | ((X1) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.56          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ sk_A @ X0)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.21/0.56          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.56          | ((X1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.56          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ sk_A @ X1)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ((X0) = (k1_xboole_0))
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.56          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ sk_A @ X1)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((sk_B_1) != (X0))
% 0.21/0.56          | ((X0) = (k1_xboole_0))
% 0.21/0.56          | ((X0) = (k1_xboole_0))
% 0.21/0.56          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.56  thf(t60_relat_1, axiom,
% 0.21/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.56  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X25 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k2_relat_1 @ X25) @ sk_A)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ X25))
% 0.21/0.56          | ~ (v1_funct_1 @ X25)
% 0.21/0.56          | ~ (v1_relat_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.56        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.56        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.56        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ?[B:$i]:
% 0.21/0.56       ( ( ![C:$i]:
% 0.21/0.56           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.56             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.56         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.56  thf('28', plain, (![X21 : $i]: ((k1_relat_1 @ (sk_B @ X21)) = (X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.56  thf(t64_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X17 : $i]:
% 0.21/0.56         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.21/0.56          | ((X17) = (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) != (k1_xboole_0))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.56          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.56  thf('34', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.56  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.56  thf('37', plain, (![X21 : $i]: (v1_funct_1 @ (sk_B @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.56  thf('38', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.56      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('40', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '27', '35', '38', '39'])).
% 0.21/0.56  thf('41', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['23', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X0)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k4_tarski @ (sk_C_2 @ X0 @ sk_A) @ (sk_D @ X0 @ sk_A)) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.56          | (r2_hidden @ X10 @ X13)
% 0.21/0.56          | ((X13) != (k1_relat_1 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.21/0.56          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ X1 @ sk_A) @ X1)
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ X1 @ sk_A) @ (k1_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ (k1_relat_1 @ X0) @ sk_A) @ (k1_relat_1 @ X0))
% 0.21/0.56          | ((k1_relat_1 @ X0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('eq_fact', [status(thm)], ['47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ (k1_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.21/0.56          | ((k1_relat_1 @ (sk_C_3 @ X1 @ X0)) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['0', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]: ((k1_relat_1 @ (sk_C_3 @ X18 @ X19)) = (X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]: ((k1_relat_1 @ (sk_C_3 @ X18 @ X19)) = (X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X0)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.56  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ (k1_relat_1 @ X0) @ sk_A) @ (k1_relat_1 @ X0))
% 0.21/0.56          | ((k1_relat_1 @ X0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('eq_fact', [status(thm)], ['47'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ (k1_relat_1 @ k1_xboole_0))
% 0.21/0.56        | ((k1_relat_1 @ k1_xboole_0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('57', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.56        | ((k1_xboole_0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.56  thf('59', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_xboole_0) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_A) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X5 : $i, X8 : $i]:
% 0.21/0.56         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_xboole_0) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | ((sk_C_2 @ k1_xboole_0 @ sk_A) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_xboole_0) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | ((sk_C_2 @ k1_xboole_0 @ sk_A) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (X1))
% 0.21/0.56          | ((k1_xboole_0) = (k1_relat_1 @ sk_A))
% 0.21/0.56          | ((k1_xboole_0) = (k1_relat_1 @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k1_xboole_0) = (k1_relat_1 @ sk_A)) | ((X0) = (X1)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.56  thf('68', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_A))),
% 0.21/0.56      inference('condensation', [status(thm)], ['67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['52', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_C_2 @ sk_A @ sk_A) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.56  thf('72', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('75', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X25 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k2_relat_1 @ X25) @ sk_A)
% 0.21/0.56          | ((sk_B_1) != (k1_relat_1 @ X25))
% 0.21/0.56          | ~ (v1_funct_1 @ X25)
% 0.21/0.56          | ~ (v1_relat_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.56         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.56         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('82', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('85', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('86', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['84', '85'])).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('88', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.56  thf('89', plain,
% 0.21/0.56      ((((sk_B @ sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['87', '88'])).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('91', plain,
% 0.21/0.56      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.56  thf('92', plain, (![X21 : $i]: (v1_funct_1 @ (sk_B @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.56  thf('93', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['91', '92'])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('95', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['94', '95'])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.56  thf('99', plain,
% 0.21/0.56      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['80', '83', '86', '93', '98'])).
% 0.21/0.56  thf('100', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['99'])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('split', [status(esa)], ['72'])).
% 0.21/0.56  thf('102', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['100', '101'])).
% 0.21/0.56  thf('103', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['73', '102'])).
% 0.21/0.56  thf('104', plain, (![X0 : $i]: (r2_hidden @ (sk_C_2 @ sk_A @ sk_A) @ X0)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['71', '103'])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      (![X5 : $i, X8 : $i]:
% 0.21/0.56         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf('106', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ sk_A) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.56  thf('107', plain, (![X0 : $i]: ((sk_C_2 @ sk_A @ sk_A) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.56  thf('108', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['106', '107'])).
% 0.21/0.56  thf('109', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '27', '35', '38', '39'])).
% 0.21/0.56  thf('110', plain, (![X0 : $i]: ((sk_B_1) != (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.56  thf('111', plain, ($false), inference('simplify', [status(thm)], ['110'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
