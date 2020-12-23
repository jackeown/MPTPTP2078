%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YxMU9FcAJw

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 201 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  832 (1821 expanded)
%              Number of equality atoms :  135 ( 311 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

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

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
        = X21 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

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

thf('34',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('44',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('45',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('54',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('61',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','67'])).

thf('69',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('71',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('72',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('81',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','81'])).

thf('83',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('84',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('85',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['50','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('92',plain,(
    $false ),
    inference('sup-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YxMU9FcAJw
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:19 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 76 iterations in 0.042s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(np__1_type, type, np__1: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.51  thf(t2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.51       ( ( A ) = ( B ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((X5) = (X4))
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.21/0.51          | ((X14) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf(t152_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.51  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.51  thf(t15_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ?[C:$i]:
% 0.21/0.51           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.51             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.51             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (sk_C_3 @ X20 @ X21)) = (X21))
% 0.21/0.51          | ((X21) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         ((v1_relat_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (sk_C_3 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf(d1_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.51          | ((X10) = (X7))
% 0.21/0.51          | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X7 : $i, X10 : $i]:
% 0.21/0.51         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1)
% 0.21/0.51          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (sk_C_3 @ X20 @ X21)) = (k1_tarski @ X20))
% 0.21/0.51          | ((X21) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.51  thf(t18_funct_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.51                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.51                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.21/0.51          | ~ (v1_funct_1 @ X22)
% 0.21/0.51          | ~ (v1_relat_1 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.51          | ((X1) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.21/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X0)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.21/0.51          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.51          | ((X1) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X1)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X0) = (k1_xboole_0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X1)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.51          | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((sk_B_1) != (X0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | ((X0) = (k1_xboole_0))
% 0.21/0.51          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf(t60_relat_1, axiom,
% 0.21/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('28', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.21/0.51          | ~ (v1_funct_1 @ X22)
% 0.21/0.51          | ~ (v1_relat_1 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('31', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51        | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.51  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ?[B:$i]:
% 0.21/0.51       ( ( ![C:$i]:
% 0.21/0.51           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.21/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.51  thf('34', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf(t64_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X17 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.21/0.51          | ((X17) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) != (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.51          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.51  thf('40', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '41'])).
% 0.21/0.51  thf('43', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.51  thf('44', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('45', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '45'])).
% 0.21/0.51  thf('47', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['27', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((sk_A) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.51  thf('51', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('54', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.21/0.51          | ((sk_B_1) != (k1_relat_1 @ X22))
% 0.21/0.51          | ~ (v1_funct_1 @ X22)
% 0.21/0.51          | ~ (v1_relat_1 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.51         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('61', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.51         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '62', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.51  thf('70', plain, (![X18 : $i]: ((k1_relat_1 @ (sk_B @ X18)) = (X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X17 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.21/0.51          | ((X17) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.21/0.51           | ~ (v1_relat_1 @ X0)
% 0.21/0.51           | ((X0) = (k1_xboole_0))))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.21/0.51           | ~ (v1_relat_1 @ X0)
% 0.21/0.51           | ((X0) = (sk_B_1))))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((X0) != (sk_B_1))
% 0.21/0.51           | ((sk_B @ X0) = (sk_B_1))
% 0.21/0.51           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['70', '75'])).
% 0.21/0.51  thf('77', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.21/0.51         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.51  thf('80', plain, (![X18 : $i]: (v1_relat_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('81', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['69', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.51  thf('84', plain, (![X18 : $i]: (v1_funct_1 @ (sk_B @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.51  thf('85', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '85'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.51      inference('split', [status(esa)], ['51'])).
% 0.21/0.51  thf('88', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['52', '88'])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['50', '89'])).
% 0.21/0.51  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('92', plain, ($false), inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
