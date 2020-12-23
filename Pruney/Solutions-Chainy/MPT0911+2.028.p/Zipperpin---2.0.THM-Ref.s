%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YpizXM5vH2

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:59 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 297 expanded)
%              Number of leaves         :   34 ( 102 expanded)
%              Depth                    :   25
%              Number of atoms          : 1298 (4989 expanded)
%              Number of equality atoms :  165 ( 710 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35
        = ( k4_tarski @ ( k1_mcart_1 @ X35 ) @ ( k2_mcart_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X41: $i,X42: $i,X43: $i,X45: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ X45 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('15',plain,(
    ! [X41: $i,X42: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X41 @ X42 @ k1_xboole_0 @ X45 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i,X45: $i] :
      ( ( X45 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ X45 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44 )
       != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33'])).

thf('37',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('40',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35
        = ( k4_tarski @ ( k1_mcart_1 @ X35 ) @ ( k2_mcart_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X21 @ X22 @ X23 @ X24 ) @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('51',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X50 @ X49 @ X51 ) )
      | ( sk_D = X51 )
      | ~ ( m1_subset_1 @ X51 @ sk_C )
      | ~ ( m1_subset_1 @ X50 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X17 @ X18 @ X19 @ X20 ) @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('65',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('77',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X25 @ X26 @ X27 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('78',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X37 @ X38 @ X40 @ X39 )
        = ( k2_mcart_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k3_zfmisc_1 @ X37 @ X38 @ X40 ) )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('81',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['78','85'])).

thf('87',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84'])).

thf('91',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( ( k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44 )
       != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','105'])).

thf('107',plain,(
    $false ),
    inference(simplify,[status(thm)],['106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YpizXM5vH2
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 1319 iterations in 0.801s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.25  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.05/1.25  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.05/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.05/1.25  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.05/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.25  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.05/1.25  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.05/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.25  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.05/1.25  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.05/1.25  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.05/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.25  thf(sk_E_type, type, sk_E: $i).
% 1.05/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.25  thf(t71_mcart_1, conjecture,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25       ( ( ![F:$i]:
% 1.05/1.25           ( ( m1_subset_1 @ F @ A ) =>
% 1.05/1.25             ( ![G:$i]:
% 1.05/1.25               ( ( m1_subset_1 @ G @ B ) =>
% 1.05/1.25                 ( ![H:$i]:
% 1.05/1.25                   ( ( m1_subset_1 @ H @ C ) =>
% 1.05/1.25                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.05/1.25                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.05/1.25         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.25           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.05/1.25           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.05/1.25        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25          ( ( ![F:$i]:
% 1.05/1.25              ( ( m1_subset_1 @ F @ A ) =>
% 1.05/1.25                ( ![G:$i]:
% 1.05/1.25                  ( ( m1_subset_1 @ G @ B ) =>
% 1.05/1.25                    ( ![H:$i]:
% 1.05/1.25                      ( ( m1_subset_1 @ H @ C ) =>
% 1.05/1.25                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.05/1.25                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.05/1.25            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.25              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.05/1.25              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.05/1.25  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('1', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t2_subset, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ A @ B ) =>
% 1.05/1.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (![X3 : $i, X4 : $i]:
% 1.05/1.25         ((r2_hidden @ X3 @ X4)
% 1.05/1.25          | (v1_xboole_0 @ X4)
% 1.05/1.25          | ~ (m1_subset_1 @ X3 @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [t2_subset])).
% 1.05/1.25  thf('3', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.25  thf(t23_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( v1_relat_1 @ B ) =>
% 1.05/1.25       ( ( r2_hidden @ A @ B ) =>
% 1.05/1.25         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (![X35 : $i, X36 : $i]:
% 1.05/1.25         (((X35) = (k4_tarski @ (k1_mcart_1 @ X35) @ (k2_mcart_1 @ X35)))
% 1.05/1.25          | ~ (v1_relat_1 @ X36)
% 1.05/1.25          | ~ (r2_hidden @ X35 @ X36))),
% 1.05/1.25      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.25  thf(d3_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.05/1.25       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 1.05/1.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.05/1.25  thf(fc6_relat_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['6', '7'])).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('demod', [status(thm)], ['5', '8'])).
% 1.05/1.25  thf(l13_xboole_0, axiom,
% 1.05/1.25    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.05/1.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['9', '10'])).
% 1.05/1.25  thf(d4_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.05/1.25       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 1.05/1.25           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)
% 1.05/1.25            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['11', '12'])).
% 1.05/1.25  thf(t55_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.05/1.25         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.05/1.25       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.05/1.25  thf('14', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X43 : $i, X45 : $i]:
% 1.05/1.25         (((X43) != (k1_xboole_0))
% 1.05/1.25          | ((k4_zfmisc_1 @ X41 @ X42 @ X43 @ X45) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X45 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X41 @ X42 @ k1_xboole_0 @ X45) = (k1_xboole_0))),
% 1.05/1.25      inference('simplify', [status(thm)], ['14'])).
% 1.05/1.25  thf('16', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 1.05/1.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 1.05/1.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.05/1.25           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.05/1.25      inference('sup+', [status(thm)], ['16', '17'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 1.05/1.25           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.05/1.25           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.05/1.25      inference('demod', [status(thm)], ['18', '19'])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 1.05/1.25           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 1.05/1.25           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.05/1.25      inference('sup+', [status(thm)], ['20', '21'])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         ((k1_xboole_0)
% 1.05/1.25           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['15', '22'])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X43 : $i, X45 : $i]:
% 1.05/1.25         (((X45) != (k1_xboole_0))
% 1.05/1.25          | ((k4_zfmisc_1 @ X41 @ X42 @ X43 @ X45) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X41 @ X42 @ X43 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.25      inference('simplify', [status(thm)], ['24'])).
% 1.05/1.25  thf('26', plain,
% 1.05/1.25      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['23', '25'])).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0) = (k1_xboole_0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('demod', [status(thm)], ['13', '26'])).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.05/1.25         (((k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44) != (k1_xboole_0))
% 1.05/1.25          | ((X44) = (k1_xboole_0))
% 1.05/1.25          | ((X43) = (k1_xboole_0))
% 1.05/1.25          | ((X42) = (k1_xboole_0))
% 1.05/1.25          | ((X41) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k1_xboole_0) != (k1_xboole_0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.05/1.25          | ((sk_A) = (k1_xboole_0))
% 1.05/1.25          | ((sk_B) = (k1_xboole_0))
% 1.05/1.25          | ((sk_C) = (k1_xboole_0))
% 1.05/1.25          | ((X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['27', '28'])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((X0) = (k1_xboole_0))
% 1.05/1.25          | ((sk_C) = (k1_xboole_0))
% 1.05/1.25          | ((sk_B) = (k1_xboole_0))
% 1.05/1.25          | ((sk_A) = (k1_xboole_0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.25  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('34', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((X0) = (k1_xboole_0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 1.05/1.25  thf('35', plain,
% 1.05/1.25      ((((k1_xboole_0) != (sk_E))
% 1.05/1.25        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['34'])).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((X0) = (k1_xboole_0))
% 1.05/1.25          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 1.05/1.25  thf('37', plain,
% 1.05/1.25      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.05/1.25      inference('clc', [status(thm)], ['35', '36'])).
% 1.05/1.25  thf('38', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.25  thf('39', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.25         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 1.05/1.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.05/1.25  thf(t10_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.05/1.25       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.05/1.25         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.05/1.25  thf('40', plain,
% 1.05/1.25      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.05/1.25         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 1.05/1.25          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.05/1.25  thf('41', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.05/1.25          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.25  thf('42', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['38', '41'])).
% 1.05/1.25  thf('43', plain,
% 1.05/1.25      (![X35 : $i, X36 : $i]:
% 1.05/1.25         (((X35) = (k4_tarski @ (k1_mcart_1 @ X35) @ (k2_mcart_1 @ X35)))
% 1.05/1.25          | ~ (v1_relat_1 @ X36)
% 1.05/1.25          | ~ (r2_hidden @ X35 @ X36))),
% 1.05/1.25      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.05/1.25  thf('44', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.05/1.25        | ((k1_mcart_1 @ sk_E)
% 1.05/1.25            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.05/1.25               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['42', '43'])).
% 1.05/1.25  thf('45', plain,
% 1.05/1.25      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.05/1.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.25  thf('46', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ((k1_mcart_1 @ sk_E)
% 1.05/1.25            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.05/1.25               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.05/1.25      inference('demod', [status(thm)], ['44', '45'])).
% 1.05/1.25  thf(d3_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.05/1.25  thf('47', plain,
% 1.05/1.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.25         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 1.05/1.25           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.05/1.25  thf('48', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.05/1.25            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.05/1.25            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.05/1.25          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['46', '47'])).
% 1.05/1.25  thf('49', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(dt_k6_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 1.05/1.25  thf('50', plain,
% 1.05/1.25      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k6_mcart_1 @ X21 @ X22 @ X23 @ X24) @ X22)
% 1.05/1.25          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 1.05/1.25  thf('51', plain,
% 1.05/1.25      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 1.05/1.25      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf('52', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t50_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.05/1.25          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.05/1.25          ( ~( ![D:$i]:
% 1.05/1.25               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.05/1.25                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.05/1.25                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.05/1.25                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.05/1.25                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.05/1.25  thf('53', plain,
% 1.05/1.25      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.05/1.25         (((X37) = (k1_xboole_0))
% 1.05/1.25          | ((X38) = (k1_xboole_0))
% 1.05/1.25          | ((k6_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 1.05/1.25              = (k2_mcart_1 @ (k1_mcart_1 @ X39)))
% 1.05/1.25          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 1.05/1.25          | ((X40) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.05/1.25  thf('54', plain,
% 1.05/1.25      ((((sk_C) = (k1_xboole_0))
% 1.05/1.25        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.05/1.25            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.05/1.25        | ((sk_B) = (k1_xboole_0))
% 1.05/1.25        | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['52', '53'])).
% 1.05/1.25  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('58', plain,
% 1.05/1.25      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.05/1.25         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 1.05/1.25  thf('59', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 1.05/1.25      inference('demod', [status(thm)], ['51', '58'])).
% 1.05/1.25  thf('60', plain,
% 1.05/1.25      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X49 @ sk_B)
% 1.05/1.25          | ((sk_E) != (k3_mcart_1 @ X50 @ X49 @ X51))
% 1.05/1.25          | ((sk_D) = (X51))
% 1.05/1.25          | ~ (m1_subset_1 @ X51 @ sk_C)
% 1.05/1.25          | ~ (m1_subset_1 @ X50 @ sk_A))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('61', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.05/1.25          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.05/1.25          | ((sk_D) = (X1))
% 1.05/1.25          | ((sk_E)
% 1.05/1.25              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['59', '60'])).
% 1.05/1.25  thf('62', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.05/1.25          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25          | ((sk_D) = (X0))
% 1.05/1.25          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.05/1.25          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['48', '61'])).
% 1.05/1.25  thf('63', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(dt_k5_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 1.05/1.25  thf('64', plain,
% 1.05/1.25      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k5_mcart_1 @ X17 @ X18 @ X19 @ X20) @ X17)
% 1.05/1.25          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 1.05/1.25  thf('65', plain,
% 1.05/1.25      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 1.05/1.25      inference('sup-', [status(thm)], ['63', '64'])).
% 1.05/1.25  thf('66', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('67', plain,
% 1.05/1.25      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.05/1.25         (((X37) = (k1_xboole_0))
% 1.05/1.25          | ((X38) = (k1_xboole_0))
% 1.05/1.25          | ((k5_mcart_1 @ X37 @ X38 @ X40 @ X39)
% 1.05/1.25              = (k1_mcart_1 @ (k1_mcart_1 @ X39)))
% 1.05/1.25          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 1.05/1.25          | ((X40) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.05/1.25  thf('68', plain,
% 1.05/1.25      ((((sk_C) = (k1_xboole_0))
% 1.05/1.25        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.05/1.25            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.05/1.25        | ((sk_B) = (k1_xboole_0))
% 1.05/1.25        | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['66', '67'])).
% 1.05/1.25  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('71', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('72', plain,
% 1.05/1.25      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.05/1.25         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['68', '69', '70', '71'])).
% 1.05/1.25  thf('73', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.05/1.25      inference('demod', [status(thm)], ['65', '72'])).
% 1.05/1.25  thf('74', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.05/1.25          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25          | ((sk_D) = (X0))
% 1.05/1.25          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.05/1.25      inference('demod', [status(thm)], ['62', '73'])).
% 1.05/1.25  thf('75', plain,
% 1.05/1.25      ((((sk_E) != (sk_E))
% 1.05/1.25        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.05/1.25        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.05/1.25        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['37', '74'])).
% 1.05/1.25  thf('76', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(dt_k7_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.05/1.25       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 1.05/1.25  thf('77', plain,
% 1.05/1.25      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k7_mcart_1 @ X25 @ X26 @ X27 @ X28) @ X27)
% 1.05/1.25          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X25 @ X26 @ X27)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 1.05/1.25  thf('78', plain,
% 1.05/1.25      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 1.05/1.25      inference('sup-', [status(thm)], ['76', '77'])).
% 1.05/1.25  thf('79', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('80', plain,
% 1.05/1.25      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.05/1.25         (((X37) = (k1_xboole_0))
% 1.05/1.25          | ((X38) = (k1_xboole_0))
% 1.05/1.25          | ((k7_mcart_1 @ X37 @ X38 @ X40 @ X39) = (k2_mcart_1 @ X39))
% 1.05/1.25          | ~ (m1_subset_1 @ X39 @ (k3_zfmisc_1 @ X37 @ X38 @ X40))
% 1.05/1.25          | ((X40) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.05/1.25  thf('81', plain,
% 1.05/1.25      ((((sk_C) = (k1_xboole_0))
% 1.05/1.25        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.05/1.25        | ((sk_B) = (k1_xboole_0))
% 1.05/1.25        | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['79', '80'])).
% 1.05/1.25  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('85', plain,
% 1.05/1.25      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['81', '82', '83', '84'])).
% 1.05/1.25  thf('86', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.05/1.25      inference('demod', [status(thm)], ['78', '85'])).
% 1.05/1.25  thf('87', plain,
% 1.05/1.25      ((((sk_E) != (sk_E))
% 1.05/1.25        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.05/1.25        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.05/1.25      inference('demod', [status(thm)], ['75', '86'])).
% 1.05/1.25  thf('88', plain,
% 1.05/1.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.05/1.25        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['87'])).
% 1.05/1.25  thf('89', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('90', plain,
% 1.05/1.25      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['81', '82', '83', '84'])).
% 1.05/1.25  thf('91', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.05/1.25      inference('demod', [status(thm)], ['89', '90'])).
% 1.05/1.25  thf('92', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['88', '91'])).
% 1.05/1.25  thf('93', plain,
% 1.05/1.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf('94', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['92', '93'])).
% 1.05/1.25  thf('95', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 1.05/1.25           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.05/1.25  thf('96', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)
% 1.05/1.25           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['94', '95'])).
% 1.05/1.25  thf('97', plain,
% 1.05/1.25      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['23', '25'])).
% 1.05/1.25  thf('98', plain,
% 1.05/1.25      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0) = (k1_xboole_0))),
% 1.05/1.25      inference('demod', [status(thm)], ['96', '97'])).
% 1.05/1.25  thf('99', plain,
% 1.05/1.25      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.05/1.25         (((k4_zfmisc_1 @ X41 @ X42 @ X43 @ X44) != (k1_xboole_0))
% 1.05/1.25          | ((X44) = (k1_xboole_0))
% 1.05/1.25          | ((X43) = (k1_xboole_0))
% 1.05/1.25          | ((X42) = (k1_xboole_0))
% 1.05/1.25          | ((X41) = (k1_xboole_0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.05/1.25  thf('100', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k1_xboole_0) != (k1_xboole_0))
% 1.05/1.25          | ((sk_A) = (k1_xboole_0))
% 1.05/1.25          | ((sk_B) = (k1_xboole_0))
% 1.05/1.25          | ((sk_C) = (k1_xboole_0))
% 1.05/1.25          | ((X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['98', '99'])).
% 1.05/1.25  thf('101', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((X0) = (k1_xboole_0))
% 1.05/1.25          | ((sk_C) = (k1_xboole_0))
% 1.05/1.25          | ((sk_B) = (k1_xboole_0))
% 1.05/1.25          | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['100'])).
% 1.05/1.25  thf('102', plain, (((sk_A) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('104', plain, (((sk_C) != (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('105', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)],
% 1.05/1.25                ['101', '102', '103', '104'])).
% 1.05/1.25  thf('106', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.05/1.25      inference('demod', [status(thm)], ['0', '105'])).
% 1.05/1.25  thf('107', plain, ($false), inference('simplify', [status(thm)], ['106'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
