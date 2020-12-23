%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GLhXvzfSxt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 123 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  638 (1119 expanded)
%              Number of equality atoms :  103 ( 182 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_1 @ X19 @ X20 ) )
        = X20 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( sk_C_1 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
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
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X11 ) @ ( sk_D @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_1 @ X19 @ X20 ) )
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 ) ) ),
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
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

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

thf('18',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ sk_B_1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('34',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('35',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('36',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( sk_C_1 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_C @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('58',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('60',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GLhXvzfSxt
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 58 iterations in 0.033s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(np__1_type, type, np__1: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.48  thf(t15_funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ?[C:$i]:
% 0.19/0.48           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.19/0.48             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (sk_C_1 @ X19 @ X20)) = (X20))
% 0.19/0.48          | ((X20) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         ((v1_funct_1 @ (sk_C_1 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf(d4_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X11 : $i, X14 : $i]:
% 0.19/0.48         (((X14) = (k1_relat_1 @ X11))
% 0.19/0.48          | (r2_hidden @ 
% 0.19/0.48             (k4_tarski @ (sk_C @ X14 @ X11) @ (sk_D @ X14 @ X11)) @ X11)
% 0.19/0.48          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.48  thf(t113_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]:
% 0.19/0.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.48  thf(t152_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.19/0.48  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.48          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '6'])).
% 0.19/0.48  thf(t60_relat_1, axiom,
% 0.19/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf(l1_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | (r1_tarski @ (k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (sk_C_1 @ X19 @ X20)) = (k1_tarski @ X19))
% 0.19/0.48          | ((X20) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf(t18_funct_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.48          ( ![C:$i]:
% 0.19/0.48            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.48                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.48             ( ![C:$i]:
% 0.19/0.48               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.48                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X21 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (v1_relat_1 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ X1))
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ X0 @ X1))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_A) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B_1)
% 0.19/0.48              != (k1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.48  thf('16', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['16'])).
% 0.19/0.48  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ?[B:$i]:
% 0.19/0.48       ( ( ![C:$i]:
% 0.19/0.48           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.19/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.48  thf('18', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['16'])).
% 0.19/0.48  thf(t65_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X16 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.19/0.48          | ((k2_relat_1 @ X16) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.19/0.48           | ~ (v1_relat_1 @ X0)
% 0.19/0.48           | ((k2_relat_1 @ X0) = (k1_xboole_0))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['16'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.19/0.48           | ~ (v1_relat_1 @ X0)
% 0.19/0.48           | ((k2_relat_1 @ X0) = (sk_B_1))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          (((X0) != (sk_B_1))
% 0.19/0.48           | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))
% 0.19/0.48           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '23'])).
% 0.19/0.48  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          (((X0) != (sk_B_1)) | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      ((((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X21 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (v1_relat_1 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.19/0.48         | ~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.19/0.48         | ~ (v1_funct_1 @ (sk_B @ sk_B_1))
% 0.19/0.48         | ((sk_B_1) != (k1_relat_1 @ (sk_B @ sk_B_1)))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['16'])).
% 0.19/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.48  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('33', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('34', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('35', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 0.19/0.48  thf('37', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['16'])).
% 0.19/0.48  thf('39', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.19/0.48  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['17', '39'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1)
% 0.19/0.48            != (k1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['15', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((sk_B_1)
% 0.19/0.48              != (k1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1)
% 0.19/0.48            != (k1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         ((v1_relat_1 @ (sk_C_1 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B_1)
% 0.19/0.48              != (k1_relat_1 @ (sk_C_1 @ (sk_C @ sk_A @ k1_xboole_0) @ X0))))),
% 0.19/0.48      inference('clc', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '45'])).
% 0.19/0.48  thf('47', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.48  thf('48', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X16 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.19/0.48          | ((k2_relat_1 @ X16) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.19/0.48          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.48  thf('51', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['52'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X21 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (v1_relat_1 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.19/0.48        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.19/0.48        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.19/0.48        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.48  thf('57', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('58', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('59', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('60', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.19/0.48  thf('61', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['47', '60'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
