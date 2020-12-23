%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3V5OUoCmpl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 126 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  675 (1165 expanded)
%              Number of equality atoms :  105 ( 184 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
        = X21 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
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

thf('9',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

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

thf('22',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ sk_B_1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('38',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('40',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36','37','38','39'])).

thf('41',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('53',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('62',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('64',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3V5OUoCmpl
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 77 iterations in 0.042s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(t15_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ?[C:$i]:
% 0.20/0.51           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.51             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.51             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (((k1_relat_1 @ (sk_C_3 @ X20 @ X21)) = (X21))
% 0.20/0.51          | ((X21) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf(t2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.51       ( ( A ) = ( B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         (((X5) = (X4))
% 0.20/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.20/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.20/0.51  thf(t113_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.20/0.51          | ((X14) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.51  thf(t152_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.51  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.51          | ((k1_xboole_0) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.51          | ((X10) = (X7))
% 0.20/0.51          | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X7 : $i, X10 : $i]:
% 0.20/0.51         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (X0))
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (((k2_relat_1 @ (sk_C_3 @ X20 @ X21)) = (k1_tarski @ X20))
% 0.20/0.51          | ((X21) = (k1_xboole_0)))),
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
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X22 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.20/0.51          | ~ (v1_funct_1 @ X22)
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (sk_A))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.51  thf('20', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ?[B:$i]:
% 0.20/0.51       ( ( ![C:$i]:
% 0.20/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.51  thf('22', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf(t65_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X17 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ X17) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.51           | ~ (v1_relat_1 @ X0)
% 0.20/0.51           | ((k2_relat_1 @ X0) = (k1_xboole_0))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.51           | ~ (v1_relat_1 @ X0)
% 0.20/0.51           | ((k2_relat_1 @ X0) = (sk_B_1))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((X0) != (sk_B_1))
% 0.20/0.51           | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))
% 0.20/0.51           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '27'])).
% 0.20/0.51  thf('29', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((X0) != (sk_B_1)) | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X22 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.20/0.51          | ~ (v1_funct_1 @ X22)
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.51         | ~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.20/0.51         | ~ (v1_funct_1 @ (sk_B @ sk_B_1))
% 0.20/0.51         | ((sk_B_1) != (k1_relat_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('35', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('38', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('39', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '36', '37', '38', '39'])).
% 0.20/0.51  thf('41', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf('43', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['21', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1)
% 0.20/0.51            != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['19', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1)
% 0.20/0.51            != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.20/0.51          | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (k1_xboole_0))
% 0.20/0.51          | ((sk_B_1)
% 0.20/0.51              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.20/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '49'])).
% 0.20/0.51  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.51  thf('52', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X17 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ X17) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) != (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.51          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) != (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X22 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.20/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.20/0.51          | ~ (v1_funct_1 @ X22)
% 0.20/0.51          | ~ (v1_relat_1 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.51        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.51        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.51        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('61', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('62', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('63', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('64', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.20/0.51  thf('65', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['51', '64'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
