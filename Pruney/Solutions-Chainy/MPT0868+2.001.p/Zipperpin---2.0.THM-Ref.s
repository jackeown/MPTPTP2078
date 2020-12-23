%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ujjEfGN2T

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:15 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  177 (1187 expanded)
%              Number of leaves         :   27 ( 360 expanded)
%              Depth                    :   22
%              Number of atoms          : 1294 (11829 expanded)
%              Number of equality atoms :  141 (1365 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('11',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_C_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_B @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ X0 ) ) @ ( k2_mcart_1 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','39'])).

thf('41',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,
    ( ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( sk_C_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k2_mcart_1 @ X24 ) )
      | ( X24
       != ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != ( k2_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('52',plain,(
    ! [X29: $i,X31: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X29 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X26 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','53'])).

thf('63',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('64',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('70',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('72',plain,
    ( ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('73',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('74',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k2_mcart_1 @ k1_xboole_0 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k1_xboole_0
        = ( k4_tarski @ ( k1_mcart_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['61','68','69','70','71','75'])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X26 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('82',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('92',plain,
    ( ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('93',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('94',plain,
    ( ( ( sk_C_1
        = ( k4_tarski @ sk_C_1 @ ( k2_mcart_1 @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_mcart_1 @ X24 ) )
      | ( X24
       != ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('96',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('98',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X25 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('101',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('103',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','98'])).

thf('106',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('107',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('111',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('112',plain,
    ( ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('113',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('114',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('115',plain,
    ( ( k1_xboole_0
      = ( k1_mcart_1 @ k1_xboole_0 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('117',plain,
    ( ( ( k1_xboole_0
        = ( k4_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ k1_xboole_0 ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['104','109','110','111','115','116'])).

thf('118',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X25 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('123',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('127',plain,
    ( ( sk_C_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_1 ) @ ( k2_mcart_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('128',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('132',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('134',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('136',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['134','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['125','139'])).

thf('141',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','39'])).

thf('142',plain,(
    sk_C_1
 != ( k1_mcart_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_C_1
      = ( k2_mcart_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k1_mcart_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['42'])).

thf('144',plain,
    ( sk_C_1
    = ( k2_mcart_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['90','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['134','138'])).

thf('147',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['40','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ujjEfGN2T
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 744 iterations in 0.349s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.80  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.80  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.59/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.80  thf(t26_mcart_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.80          ( ~( ![C:$i]:
% 0.59/0.80               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.59/0.80                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.59/0.80                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.80             ( ~( ![C:$i]:
% 0.59/0.80                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.59/0.80                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.59/0.80                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.59/0.80  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(d2_subset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.80         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.80       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.80         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X15 @ X16)
% 0.59/0.80          | (r2_hidden @ X15 @ X16)
% 0.59/0.80          | (v1_xboole_0 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.80  thf(t23_mcart_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( v1_relat_1 @ B ) =>
% 0.59/0.80       ( ( r2_hidden @ A @ B ) =>
% 0.59/0.80         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X27 : $i, X28 : $i]:
% 0.59/0.80         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.59/0.80          | ~ (v1_relat_1 @ X28)
% 0.59/0.80          | ~ (r2_hidden @ X27 @ X28))),
% 0.59/0.80      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.80  thf(fc6_relat_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf(l13_xboole_0, axiom,
% 0.59/0.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.59/0.80        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (((v1_xboole_0 @ k1_xboole_0)
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.59/0.80        | (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.80  thf(l54_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.59/0.80       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.80         ((r2_hidden @ X12 @ X13)
% 0.59/0.80          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.80          | (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.80          | (r2_hidden @ (k2_mcart_1 @ sk_C_1) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | (r2_hidden @ (k2_mcart_1 @ sk_C_1) @ sk_B_1)
% 0.59/0.80        | (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '14'])).
% 0.59/0.80  thf(d1_xboole_0, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X27 : $i, X28 : $i]:
% 0.59/0.80         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.59/0.80          | ~ (v1_relat_1 @ X28)
% 0.59/0.80          | ~ (r2_hidden @ X27 @ X28))),
% 0.59/0.80      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ X0)
% 0.59/0.80          | ~ (v1_relat_1 @ X0)
% 0.59/0.80          | ((sk_B @ X0)
% 0.59/0.80              = (k4_tarski @ (k1_mcart_1 @ (sk_B @ X0)) @ 
% 0.59/0.80                 (k2_mcart_1 @ (sk_B @ X0)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.80         ((r2_hidden @ X10 @ X11)
% 0.59/0.80          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r2_hidden @ (sk_B @ X0) @ (k2_zfmisc_1 @ X2 @ X1))
% 0.59/0.80          | ~ (v1_relat_1 @ X0)
% 0.59/0.80          | (v1_xboole_0 @ X0)
% 0.59/0.80          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ X0)) @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.80          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1)
% 0.59/0.80          | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.80          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['16', '21'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.80          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1)
% 0.59/0.80          | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1)
% 0.59/0.80          | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (![X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ k1_xboole_0)
% 0.59/0.80          | ~ (v1_xboole_0 @ X1)
% 0.59/0.80          | ~ (v1_xboole_0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['29', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.80      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (((v1_xboole_0 @ k1_xboole_0)
% 0.59/0.80        | (r2_hidden @ (k2_mcart_1 @ sk_C_1) @ sk_B_1))),
% 0.59/0.80      inference('clc', [status(thm)], ['15', '32'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('35', plain, (((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.80  thf(t8_boole, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t8_boole])).
% 0.59/0.80  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((X0) != (k1_xboole_0))
% 0.59/0.80          | ~ (v1_xboole_0 @ sk_B_1)
% 0.59/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['38'])).
% 0.59/0.80  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.80      inference('clc', [status(thm)], ['35', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.59/0.80        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      ((((sk_C_1) = (k1_mcart_1 @ sk_C_1)) | ((sk_C_1) = (k2_mcart_1 @ sk_C_1)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      ((((sk_C_1) = (k2_mcart_1 @ sk_C_1)))
% 0.59/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('split', [status(esa)], ['42'])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.59/0.80        | ((sk_C_1)
% 0.59/0.80            = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1))))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf('45', plain, ((m1_subset_1 @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.64/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.80  thf('46', plain,
% 0.64/0.80      (![X16 : $i, X17 : $i]:
% 0.64/0.80         (~ (m1_subset_1 @ X17 @ X16)
% 0.64/0.80          | (v1_xboole_0 @ X17)
% 0.64/0.80          | ~ (v1_xboole_0 @ X16))),
% 0.64/0.80      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.64/0.80  thf('47', plain,
% 0.64/0.80      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | (v1_xboole_0 @ sk_C_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.64/0.80  thf('48', plain,
% 0.64/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80        | (v1_xboole_0 @ sk_C_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['44', '47'])).
% 0.64/0.80  thf('49', plain,
% 0.64/0.80      (((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ sk_C_1))
% 0.64/0.80         | (v1_xboole_0 @ sk_C_1))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup+', [status(thm)], ['43', '48'])).
% 0.64/0.80  thf(t20_mcart_1, axiom,
% 0.64/0.80    (![A:$i]:
% 0.64/0.80     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.64/0.80       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.64/0.80  thf('50', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.64/0.80         (((X24) != (k2_mcart_1 @ X24)) | ((X24) != (k4_tarski @ X25 @ X26)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.64/0.80  thf('51', plain,
% 0.64/0.80      (![X25 : $i, X26 : $i]:
% 0.64/0.80         ((k4_tarski @ X25 @ X26) != (k2_mcart_1 @ (k4_tarski @ X25 @ X26)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['50'])).
% 0.64/0.80  thf(t7_mcart_1, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.64/0.80       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.64/0.80  thf('52', plain,
% 0.64/0.80      (![X29 : $i, X31 : $i]: ((k2_mcart_1 @ (k4_tarski @ X29 @ X31)) = (X31))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.64/0.80  thf('53', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X26))),
% 0.64/0.80      inference('demod', [status(thm)], ['51', '52'])).
% 0.64/0.80  thf('54', plain,
% 0.64/0.80      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['49', '53'])).
% 0.64/0.80  thf('55', plain,
% 0.64/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.64/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.64/0.80  thf('56', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('57', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.64/0.80  thf(t7_ordinal1, axiom,
% 0.64/0.80    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.64/0.80  thf('58', plain,
% 0.64/0.80      (![X22 : $i, X23 : $i]:
% 0.64/0.80         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.64/0.80  thf('59', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.64/0.80  thf('60', plain,
% 0.64/0.80      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['56', '59'])).
% 0.64/0.80  thf('61', plain,
% 0.64/0.80      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.64/0.80         | ((sk_C_1)
% 0.64/0.80             = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['41', '60'])).
% 0.64/0.80  thf('62', plain,
% 0.64/0.80      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['49', '53'])).
% 0.64/0.80  thf('63', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('64', plain,
% 0.64/0.80      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.64/0.80  thf(d3_tarski, axiom,
% 0.64/0.80    (![A:$i,B:$i]:
% 0.64/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.64/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.64/0.80  thf('65', plain,
% 0.64/0.80      (![X4 : $i, X6 : $i]:
% 0.64/0.80         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.64/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.80  thf('66', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.80  thf('67', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.64/0.80  thf('68', plain,
% 0.64/0.80      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['64', '67'])).
% 0.64/0.80  thf('69', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('70', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('71', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('72', plain,
% 0.64/0.80      ((((sk_C_1) = (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('split', [status(esa)], ['42'])).
% 0.64/0.80  thf('73', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('74', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.64/0.80  thf('75', plain,
% 0.64/0.80      ((((k1_xboole_0) = (k2_mcart_1 @ k1_xboole_0)))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.64/0.80  thf('76', plain,
% 0.64/0.80      (((((k1_xboole_0)
% 0.64/0.80           = (k4_tarski @ (k1_mcart_1 @ k1_xboole_0) @ k1_xboole_0))
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['61', '68', '69', '70', '71', '75'])).
% 0.64/0.80  thf('77', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X26))),
% 0.64/0.80      inference('demod', [status(thm)], ['51', '52'])).
% 0.64/0.80  thf('78', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.64/0.80  thf('79', plain,
% 0.64/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.64/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.64/0.80  thf('80', plain,
% 0.64/0.80      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['78', '79'])).
% 0.64/0.80  thf('81', plain,
% 0.64/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.64/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.80  thf('82', plain,
% 0.64/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.64/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.80  thf('83', plain,
% 0.64/0.80      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.64/0.80         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.64/0.80          | ~ (r2_hidden @ X12 @ X14)
% 0.64/0.80          | ~ (r2_hidden @ X10 @ X11))),
% 0.64/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.64/0.80  thf('84', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.80         ((v1_xboole_0 @ X0)
% 0.64/0.80          | ~ (r2_hidden @ X2 @ X1)
% 0.64/0.80          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.64/0.80             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['82', '83'])).
% 0.64/0.80  thf('85', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         ((v1_xboole_0 @ X0)
% 0.64/0.80          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.64/0.80             (k2_zfmisc_1 @ X0 @ X1))
% 0.64/0.80          | (v1_xboole_0 @ X1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['81', '84'])).
% 0.64/0.80  thf('86', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.80  thf('87', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         ((v1_xboole_0 @ X0)
% 0.64/0.80          | (v1_xboole_0 @ X1)
% 0.64/0.80          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['85', '86'])).
% 0.64/0.80  thf('88', plain,
% 0.64/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.64/0.80         | (v1_xboole_0 @ sk_A)
% 0.64/0.80         | (v1_xboole_0 @ sk_B_1))) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['80', '87'])).
% 0.64/0.80  thf('89', plain,
% 0.64/0.80      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['62', '63'])).
% 0.64/0.80  thf('90', plain,
% 0.64/0.80      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['88', '89'])).
% 0.64/0.80  thf('91', plain,
% 0.64/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.64/0.80  thf('92', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_mcart_1 @ sk_C_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('split', [status(esa)], ['42'])).
% 0.64/0.80  thf('93', plain,
% 0.64/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80        | (v1_xboole_0 @ sk_C_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['44', '47'])).
% 0.64/0.80  thf('94', plain,
% 0.64/0.80      (((((sk_C_1) = (k4_tarski @ sk_C_1 @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80         | (v1_xboole_0 @ sk_C_1))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup+', [status(thm)], ['92', '93'])).
% 0.64/0.80  thf('95', plain,
% 0.64/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.64/0.80         (((X24) != (k1_mcart_1 @ X24)) | ((X24) != (k4_tarski @ X25 @ X26)))),
% 0.64/0.80      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.64/0.80  thf('96', plain,
% 0.64/0.80      (![X25 : $i, X26 : $i]:
% 0.64/0.80         ((k4_tarski @ X25 @ X26) != (k1_mcart_1 @ (k4_tarski @ X25 @ X26)))),
% 0.64/0.80      inference('simplify', [status(thm)], ['95'])).
% 0.64/0.80  thf('97', plain,
% 0.64/0.80      (![X29 : $i, X30 : $i]: ((k1_mcart_1 @ (k4_tarski @ X29 @ X30)) = (X29))),
% 0.64/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.64/0.80  thf('98', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X25))),
% 0.64/0.80      inference('demod', [status(thm)], ['96', '97'])).
% 0.64/0.80  thf('99', plain,
% 0.64/0.80      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['94', '98'])).
% 0.64/0.80  thf('100', plain,
% 0.64/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.64/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.64/0.80  thf('101', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('102', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.64/0.80  thf('103', plain,
% 0.64/0.80      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['101', '102'])).
% 0.64/0.80  thf('104', plain,
% 0.64/0.80      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.64/0.80         | ((sk_C_1)
% 0.64/0.80             = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['91', '103'])).
% 0.64/0.80  thf('105', plain,
% 0.64/0.80      (((v1_xboole_0 @ sk_C_1)) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['94', '98'])).
% 0.64/0.80  thf('106', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('107', plain,
% 0.64/0.80      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['105', '106'])).
% 0.64/0.80  thf('108', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.64/0.80  thf('109', plain,
% 0.64/0.80      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['107', '108'])).
% 0.64/0.80  thf('110', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('111', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('112', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_mcart_1 @ sk_C_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('split', [status(esa)], ['42'])).
% 0.64/0.80  thf('113', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('114', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('115', plain,
% 0.64/0.80      ((((k1_xboole_0) = (k1_mcart_1 @ k1_xboole_0)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.64/0.80  thf('116', plain,
% 0.64/0.80      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['99', '100'])).
% 0.64/0.80  thf('117', plain,
% 0.64/0.80      (((((k1_xboole_0)
% 0.64/0.80           = (k4_tarski @ k1_xboole_0 @ (k2_mcart_1 @ k1_xboole_0)))
% 0.64/0.80         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)],
% 0.64/0.80                ['104', '109', '110', '111', '115', '116'])).
% 0.64/0.80  thf('118', plain,
% 0.64/0.80      (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X25))),
% 0.64/0.80      inference('demod', [status(thm)], ['96', '97'])).
% 0.64/0.80  thf('119', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 0.64/0.80  thf('120', plain,
% 0.64/0.80      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.64/0.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.64/0.80  thf('121', plain,
% 0.64/0.80      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['119', '120'])).
% 0.64/0.80  thf('122', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         ((v1_xboole_0 @ X0)
% 0.64/0.80          | (v1_xboole_0 @ X1)
% 0.64/0.80          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['85', '86'])).
% 0.64/0.80  thf('123', plain,
% 0.64/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.64/0.80         | (v1_xboole_0 @ sk_A)
% 0.64/0.80         | (v1_xboole_0 @ sk_B_1))) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('sup-', [status(thm)], ['121', '122'])).
% 0.64/0.80  thf('124', plain,
% 0.64/0.80      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['105', '106'])).
% 0.64/0.80  thf('125', plain,
% 0.64/0.80      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.64/0.80         <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.80      inference('demod', [status(thm)], ['123', '124'])).
% 0.64/0.80  thf('126', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.64/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.64/0.80  thf('127', plain,
% 0.64/0.80      ((((sk_C_1) = (k4_tarski @ (k1_mcart_1 @ sk_C_1) @ (k2_mcart_1 @ sk_C_1)))
% 0.64/0.80        | (v1_xboole_0 @ k1_xboole_0))),
% 0.64/0.80      inference('simplify', [status(thm)], ['11'])).
% 0.64/0.80  thf('128', plain,
% 0.64/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.80         ((r2_hidden @ X10 @ X11)
% 0.64/0.80          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.64/0.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.64/0.80  thf('129', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]:
% 0.64/0.80         (~ (r2_hidden @ sk_C_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.64/0.80          | (v1_xboole_0 @ k1_xboole_0)
% 0.64/0.80          | (r2_hidden @ (k1_mcart_1 @ sk_C_1) @ X1))),
% 0.64/0.80      inference('sup-', [status(thm)], ['127', '128'])).
% 0.64/0.80  thf('130', plain,
% 0.64/0.80      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.64/0.80        | (r2_hidden @ (k1_mcart_1 @ sk_C_1) @ sk_A)
% 0.64/0.80        | (v1_xboole_0 @ k1_xboole_0))),
% 0.64/0.80      inference('sup-', [status(thm)], ['126', '129'])).
% 0.64/0.80  thf('131', plain,
% 0.64/0.80      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ k1_xboole_0))),
% 0.64/0.80      inference('simplify', [status(thm)], ['31'])).
% 0.64/0.80  thf('132', plain,
% 0.64/0.80      (((v1_xboole_0 @ k1_xboole_0)
% 0.64/0.80        | (r2_hidden @ (k1_mcart_1 @ sk_C_1) @ sk_A))),
% 0.64/0.80      inference('clc', [status(thm)], ['130', '131'])).
% 0.64/0.80  thf('133', plain,
% 0.64/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.81  thf('134', plain, (((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['132', '133'])).
% 0.64/0.81  thf('135', plain,
% 0.64/0.81      (![X8 : $i, X9 : $i]:
% 0.64/0.81         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 0.64/0.81      inference('cnf', [status(esa)], [t8_boole])).
% 0.64/0.81  thf('136', plain, (((sk_A) != (k1_xboole_0))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('137', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((X0) != (k1_xboole_0))
% 0.64/0.81          | ~ (v1_xboole_0 @ sk_A)
% 0.64/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.81      inference('sup-', [status(thm)], ['135', '136'])).
% 0.64/0.81  thf('138', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('simplify', [status(thm)], ['137'])).
% 0.64/0.81  thf('139', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('clc', [status(thm)], ['134', '138'])).
% 0.64/0.81  thf('140', plain,
% 0.64/0.81      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_C_1) = (k1_mcart_1 @ sk_C_1))))),
% 0.64/0.81      inference('clc', [status(thm)], ['125', '139'])).
% 0.64/0.81  thf('141', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.64/0.81      inference('clc', [status(thm)], ['35', '39'])).
% 0.64/0.81  thf('142', plain, (~ (((sk_C_1) = (k1_mcart_1 @ sk_C_1)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['140', '141'])).
% 0.64/0.81  thf('143', plain,
% 0.64/0.81      ((((sk_C_1) = (k2_mcart_1 @ sk_C_1))) | 
% 0.64/0.81       (((sk_C_1) = (k1_mcart_1 @ sk_C_1)))),
% 0.64/0.81      inference('split', [status(esa)], ['42'])).
% 0.64/0.81  thf('144', plain, ((((sk_C_1) = (k2_mcart_1 @ sk_C_1)))),
% 0.64/0.81      inference('sat_resolution*', [status(thm)], ['142', '143'])).
% 0.64/0.81  thf('145', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.64/0.81      inference('simpl_trail', [status(thm)], ['90', '144'])).
% 0.64/0.81  thf('146', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('clc', [status(thm)], ['134', '138'])).
% 0.64/0.81  thf('147', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.64/0.81      inference('clc', [status(thm)], ['145', '146'])).
% 0.64/0.81  thf('148', plain, ($false), inference('demod', [status(thm)], ['40', '147'])).
% 0.64/0.81  
% 0.64/0.81  % SZS output end Refutation
% 0.64/0.81  
% 0.64/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
