%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zb73MUhbMc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 175 expanded)
%              Number of leaves         :   30 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  754 (1426 expanded)
%              Number of equality atoms :  108 ( 226 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25
        = ( k2_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X25 @ X22 ) @ ( sk_C_3 @ X25 @ X22 ) ) @ X22 )
      | ( r2_hidden @ ( sk_C_3 @ X25 @ X22 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X28 @ X29 ) )
        = X29 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X28 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X28 @ X29 ) )
        = ( k1_tarski @ X28 ) )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('30',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('31',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('37',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ X17 )
      | ( r2_hidden @ ( sk_B @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    ! [X27: $i] :
      ( ( v1_funct_1 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('59',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('62',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('65',plain,
    ( ( sk_B_1
      = ( k1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60','65'])).

thf('67',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ X17 )
      | ( r2_hidden @ ( sk_B @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('76',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('84',plain,(
    $false ),
    inference('sup-',[status(thm)],['82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zb73MUhbMc
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 98 iterations in 0.040s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(d5_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X22 : $i, X25 : $i]:
% 0.21/0.50         (((X25) = (k2_relat_1 @ X22))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k4_tarski @ (sk_D_1 @ X25 @ X22) @ (sk_C_3 @ X25 @ X22)) @ X22)
% 0.21/0.50          | (r2_hidden @ (sk_C_3 @ X25 @ X22) @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.50  thf(t113_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.50          | ((X12) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.50  thf(t152_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.50  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.50          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.50  thf(t60_relat_1, axiom,
% 0.21/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t15_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ?[C:$i]:
% 0.21/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         (((k1_relat_1 @ (sk_C_4 @ X28 @ X29)) = (X29))
% 0.21/0.50          | ((X29) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (sk_C_4 @ X28 @ X29)) | ((X29) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         ((v1_funct_1 @ (sk_C_4 @ X28 @ X29)) | ((X29) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf(d1_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X5 : $i, X8 : $i]:
% 0.21/0.50         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.50          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ X0 @ X1)
% 0.21/0.50          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         (((k2_relat_1 @ (sk_C_4 @ X28 @ X29)) = (k1_tarski @ X28))
% 0.21/0.50          | ((X29) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.50  thf(t18_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.50                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.50                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X30 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ X30) @ sk_A)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ X30))
% 0.21/0.50          | ~ (v1_funct_1 @ X30)
% 0.21/0.50          | ~ (v1_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ sk_A @ X0)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.21/0.50          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.50          | ((X1) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ sk_A @ X1)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ sk_A @ X1)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((sk_B_1) != (X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf(cc1_funct_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.21/0.50  thf('30', plain, (![X27 : $i]: ((v1_funct_1 @ X27) | ~ (v1_xboole_0 @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.50  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X30 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ X30) @ sk_A)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ X30))
% 0.21/0.50          | ~ (v1_funct_1 @ X30)
% 0.21/0.50          | ~ (v1_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('34', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50        | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.50  thf(d1_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.50              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X17 : $i]: ((v1_relat_1 @ X17) | (r2_hidden @ (sk_B @ X17) @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.50  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '40'])).
% 0.21/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.50  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['29', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_A) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '46'])).
% 0.21/0.50  thf('48', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('50', plain, (![X27 : $i]: ((v1_funct_1 @ X27) | ~ (v1_xboole_0 @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X30 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ X30) @ sk_A)
% 0.21/0.50          | ((sk_B_1) != (k1_relat_1 @ X30))
% 0.21/0.50          | ~ (v1_funct_1 @ X30)
% 0.21/0.50          | ~ (v1_relat_1 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.50         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('59', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('62', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_relat_1 @ sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['63', '64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['57', '60', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['68', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X17 : $i]: ((v1_relat_1 @ X17) | (r2_hidden @ (sk_B @ X17) @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.21/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['73', '76'])).
% 0.21/0.50  thf('78', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['72', '77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('split', [status(esa)], ['48'])).
% 0.21/0.50  thf('80', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.21/0.50  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['49', '80'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (![X0 : $i]: (r2_hidden @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['47', '81'])).
% 0.21/0.50  thf('83', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('84', plain, ($false), inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
