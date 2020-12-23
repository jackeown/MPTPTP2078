%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.petMWTPEWC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:00 EST 2020

% Result     : Theorem 13.22s
% Output     : Refutation 13.22s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 448 expanded)
%              Number of leaves         :   34 ( 148 expanded)
%              Depth                    :   33
%              Number of atoms          : 1705 (6211 expanded)
%              Number of equality atoms :  225 ( 832 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k4_tarski @ ( k1_mcart_1 @ X23 ) @ ( k2_mcart_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( X31 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X33 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ k1_xboole_0 @ X33 )
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
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( X33 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X33 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ k1_xboole_0 )
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
       != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k4_tarski @ ( k1_mcart_1 @ X23 ) @ ( k2_mcart_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
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

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('55',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) )
      | ( sk_D = X39 )
      | ~ ( m1_subset_1 @ X39 @ sk_C )
      | ~ ( m1_subset_1 @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
       != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('88',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k2_mcart_1 @ X20 ) )
      | ( X20
       != ( k4_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_tarski @ X21 @ X22 )
     != ( k2_mcart_1 @ ( k4_tarski @ X21 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('90',plain,(
    ! [X34: $i,X36: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X34 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('91',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_tarski @ X21 @ X22 )
     != X22 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','94'])).

thf('96',plain,
    ( ( sk_E != sk_E )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('103',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
       != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( sk_E != sk_E )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','119'])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
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

thf('124',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X25 @ X26 @ X28 @ X27 )
        = ( k2_mcart_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k3_zfmisc_1 @ X25 @ X26 @ X28 ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('125',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['122','129'])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['121','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('133',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
       != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','144'])).

thf('146',plain,(
    $false ),
    inference(simplify,[status(thm)],['145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.petMWTPEWC
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 13.22/13.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.22/13.43  % Solved by: fo/fo7.sh
% 13.22/13.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.22/13.43  % done 15986 iterations in 12.991s
% 13.22/13.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.22/13.43  % SZS output start Refutation
% 13.22/13.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.22/13.43  thf(sk_A_type, type, sk_A: $i).
% 13.22/13.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.22/13.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 13.22/13.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.22/13.43  thf(sk_C_type, type, sk_C: $i).
% 13.22/13.43  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 13.22/13.43  thf(sk_D_type, type, sk_D: $i).
% 13.22/13.43  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 13.22/13.43  thf(sk_B_type, type, sk_B: $i).
% 13.22/13.43  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 13.22/13.43  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 13.22/13.43  thf(sk_E_type, type, sk_E: $i).
% 13.22/13.43  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 13.22/13.43  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 13.22/13.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.22/13.43  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 13.22/13.43  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 13.22/13.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.22/13.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.22/13.43  thf(t71_mcart_1, conjecture,
% 13.22/13.43    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.22/13.43     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 13.22/13.43       ( ( ![F:$i]:
% 13.22/13.43           ( ( m1_subset_1 @ F @ A ) =>
% 13.22/13.43             ( ![G:$i]:
% 13.22/13.43               ( ( m1_subset_1 @ G @ B ) =>
% 13.22/13.43                 ( ![H:$i]:
% 13.22/13.43                   ( ( m1_subset_1 @ H @ C ) =>
% 13.22/13.43                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 13.22/13.43                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 13.22/13.43         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.22/13.43           ( ( C ) = ( k1_xboole_0 ) ) | 
% 13.22/13.43           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 13.22/13.43  thf(zf_stmt_0, negated_conjecture,
% 13.22/13.43    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.22/13.43        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 13.22/13.43          ( ( ![F:$i]:
% 13.22/13.43              ( ( m1_subset_1 @ F @ A ) =>
% 13.22/13.43                ( ![G:$i]:
% 13.22/13.43                  ( ( m1_subset_1 @ G @ B ) =>
% 13.22/13.43                    ( ![H:$i]:
% 13.22/13.43                      ( ( m1_subset_1 @ H @ C ) =>
% 13.22/13.43                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 13.22/13.43                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 13.22/13.43            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.22/13.43              ( ( C ) = ( k1_xboole_0 ) ) | 
% 13.22/13.43              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 13.22/13.43    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 13.22/13.43  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('1', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf(t2_subset, axiom,
% 13.22/13.43    (![A:$i,B:$i]:
% 13.22/13.43     ( ( m1_subset_1 @ A @ B ) =>
% 13.22/13.43       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 13.22/13.43  thf('2', plain,
% 13.22/13.43      (![X3 : $i, X4 : $i]:
% 13.22/13.43         ((r2_hidden @ X3 @ X4)
% 13.22/13.43          | (v1_xboole_0 @ X4)
% 13.22/13.43          | ~ (m1_subset_1 @ X3 @ X4))),
% 13.22/13.43      inference('cnf', [status(esa)], [t2_subset])).
% 13.22/13.43  thf('3', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['1', '2'])).
% 13.22/13.43  thf(t23_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i]:
% 13.22/13.43     ( ( v1_relat_1 @ B ) =>
% 13.22/13.43       ( ( r2_hidden @ A @ B ) =>
% 13.22/13.43         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 13.22/13.43  thf('4', plain,
% 13.22/13.43      (![X23 : $i, X24 : $i]:
% 13.22/13.43         (((X23) = (k4_tarski @ (k1_mcart_1 @ X23) @ (k2_mcart_1 @ X23)))
% 13.22/13.43          | ~ (v1_relat_1 @ X24)
% 13.22/13.43          | ~ (r2_hidden @ X23 @ X24))),
% 13.22/13.43      inference('cnf', [status(esa)], [t23_mcart_1])).
% 13.22/13.43  thf('5', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('sup-', [status(thm)], ['3', '4'])).
% 13.22/13.43  thf(d3_zfmisc_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i]:
% 13.22/13.43     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 13.22/13.43       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 13.22/13.43  thf('6', plain,
% 13.22/13.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 13.22/13.43           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 13.22/13.43  thf(fc6_relat_1, axiom,
% 13.22/13.43    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 13.22/13.43  thf('7', plain,
% 13.22/13.43      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 13.22/13.43      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.22/13.43  thf('8', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.43         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 13.22/13.43      inference('sup+', [status(thm)], ['6', '7'])).
% 13.22/13.43  thf('9', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('demod', [status(thm)], ['5', '8'])).
% 13.22/13.43  thf(l13_xboole_0, axiom,
% 13.22/13.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 13.22/13.43  thf('10', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('11', plain,
% 13.22/13.43      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['9', '10'])).
% 13.22/13.43  thf(d4_zfmisc_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i,D:$i]:
% 13.22/13.43     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 13.22/13.43       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 13.22/13.43  thf('12', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('13', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)
% 13.22/13.43            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('sup+', [status(thm)], ['11', '12'])).
% 13.22/13.43  thf(t55_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i,D:$i]:
% 13.22/13.43     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 13.22/13.43         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 13.22/13.43       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 13.22/13.43  thf('14', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 13.22/13.43         (((X31) != (k1_xboole_0))
% 13.22/13.43          | ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X33) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('15', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X33 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X29 @ X30 @ k1_xboole_0 @ X33) = (k1_xboole_0))),
% 13.22/13.43      inference('simplify', [status(thm)], ['14'])).
% 13.22/13.43  thf('16', plain,
% 13.22/13.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 13.22/13.43           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 13.22/13.43  thf('17', plain,
% 13.22/13.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 13.22/13.43           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 13.22/13.43  thf('18', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 13.22/13.43      inference('sup+', [status(thm)], ['16', '17'])).
% 13.22/13.43  thf('19', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('20', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 13.22/13.43           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 13.22/13.43      inference('demod', [status(thm)], ['18', '19'])).
% 13.22/13.43  thf('21', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('22', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 13.22/13.43           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 13.22/13.43      inference('sup+', [status(thm)], ['20', '21'])).
% 13.22/13.43  thf('23', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.22/13.43         ((k1_xboole_0)
% 13.22/13.43           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 13.22/13.43      inference('sup+', [status(thm)], ['15', '22'])).
% 13.22/13.43  thf('24', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 13.22/13.43         (((X33) != (k1_xboole_0))
% 13.22/13.43          | ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X33) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('25', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 13.22/13.43      inference('simplify', [status(thm)], ['24'])).
% 13.22/13.43  thf('26', plain,
% 13.22/13.43      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('demod', [status(thm)], ['23', '25'])).
% 13.22/13.43  thf('27', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('demod', [status(thm)], ['13', '26'])).
% 13.22/13.43  thf('28', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32) != (k1_xboole_0))
% 13.22/13.43          | ((X32) = (k1_xboole_0))
% 13.22/13.43          | ((X31) = (k1_xboole_0))
% 13.22/13.43          | ((X30) = (k1_xboole_0))
% 13.22/13.43          | ((X29) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('29', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (k1_xboole_0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((X0) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['27', '28'])).
% 13.22/13.43  thf('30', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('simplify', [status(thm)], ['29'])).
% 13.22/13.43  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('34', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 13.22/13.43  thf('35', plain,
% 13.22/13.43      ((((k1_xboole_0) != (sk_E))
% 13.22/13.43        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('eq_fact', [status(thm)], ['34'])).
% 13.22/13.43  thf('36', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 13.22/13.43  thf('37', plain,
% 13.22/13.43      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 13.22/13.43      inference('clc', [status(thm)], ['35', '36'])).
% 13.22/13.43  thf('38', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['1', '2'])).
% 13.22/13.43  thf('39', plain,
% 13.22/13.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 13.22/13.43           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 13.22/13.43  thf(t10_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i]:
% 13.22/13.43     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 13.22/13.43       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 13.22/13.43         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 13.22/13.43  thf('40', plain,
% 13.22/13.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 13.22/13.43         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 13.22/13.43          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t10_mcart_1])).
% 13.22/13.43  thf('41', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.22/13.43         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['39', '40'])).
% 13.22/13.43  thf('42', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['38', '41'])).
% 13.22/13.43  thf('43', plain,
% 13.22/13.43      (![X23 : $i, X24 : $i]:
% 13.22/13.43         (((X23) = (k4_tarski @ (k1_mcart_1 @ X23) @ (k2_mcart_1 @ X23)))
% 13.22/13.43          | ~ (v1_relat_1 @ X24)
% 13.22/13.43          | ~ (r2_hidden @ X23 @ X24))),
% 13.22/13.43      inference('cnf', [status(esa)], [t23_mcart_1])).
% 13.22/13.43  thf('44', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 13.22/13.43        | ((k1_mcart_1 @ sk_E)
% 13.22/13.43            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 13.22/13.43               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 13.22/13.43      inference('sup-', [status(thm)], ['42', '43'])).
% 13.22/13.43  thf('45', plain,
% 13.22/13.43      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 13.22/13.43      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.22/13.43  thf('46', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ((k1_mcart_1 @ sk_E)
% 13.22/13.43            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 13.22/13.43               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 13.22/13.43      inference('demod', [status(thm)], ['44', '45'])).
% 13.22/13.43  thf(d3_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i]:
% 13.22/13.43     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 13.22/13.43  thf('47', plain,
% 13.22/13.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.22/13.43         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 13.22/13.43           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_mcart_1])).
% 13.22/13.43  thf('48', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 13.22/13.43            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 13.22/13.43            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 13.22/13.43          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('sup+', [status(thm)], ['46', '47'])).
% 13.22/13.43  thf('49', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['38', '41'])).
% 13.22/13.43  thf('50', plain,
% 13.22/13.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 13.22/13.43         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 13.22/13.43          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t10_mcart_1])).
% 13.22/13.43  thf('51', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 13.22/13.43      inference('sup-', [status(thm)], ['49', '50'])).
% 13.22/13.43  thf('52', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('53', plain,
% 13.22/13.43      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['51', '52'])).
% 13.22/13.43  thf(t1_subset, axiom,
% 13.22/13.43    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 13.22/13.43  thf('54', plain,
% 13.22/13.43      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 13.22/13.43      inference('cnf', [status(esa)], [t1_subset])).
% 13.22/13.43  thf('55', plain,
% 13.22/13.43      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 13.22/13.43        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 13.22/13.43      inference('sup-', [status(thm)], ['53', '54'])).
% 13.22/13.43  thf('56', plain,
% 13.22/13.43      (![X37 : $i, X38 : $i, X39 : $i]:
% 13.22/13.43         (~ (m1_subset_1 @ X37 @ sk_B)
% 13.22/13.43          | ((sk_E) != (k3_mcart_1 @ X38 @ X37 @ X39))
% 13.22/13.43          | ((sk_D) = (X39))
% 13.22/13.43          | ~ (m1_subset_1 @ X39 @ sk_C)
% 13.22/13.43          | ~ (m1_subset_1 @ X38 @ sk_A))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('57', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 13.22/13.43          | ~ (m1_subset_1 @ X0 @ sk_A)
% 13.22/13.43          | ~ (m1_subset_1 @ X1 @ sk_C)
% 13.22/13.43          | ((sk_D) = (X1))
% 13.22/13.43          | ((sk_E)
% 13.22/13.43              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['55', '56'])).
% 13.22/13.43  thf('58', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 13.22/13.43          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43          | ((sk_D) = (X0))
% 13.22/13.43          | ~ (m1_subset_1 @ X0 @ sk_C)
% 13.22/13.43          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['48', '57'])).
% 13.22/13.43  thf('59', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['38', '41'])).
% 13.22/13.43  thf('60', plain,
% 13.22/13.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 13.22/13.43         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 13.22/13.43          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t10_mcart_1])).
% 13.22/13.43  thf('61', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 13.22/13.43      inference('sup-', [status(thm)], ['59', '60'])).
% 13.22/13.43  thf('62', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 13.22/13.43      inference('sup-', [status(thm)], ['59', '60'])).
% 13.22/13.43  thf('63', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('64', plain,
% 13.22/13.43      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('demod', [status(thm)], ['23', '25'])).
% 13.22/13.43  thf('65', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('sup+', [status(thm)], ['63', '64'])).
% 13.22/13.43  thf('66', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('67', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.43         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 13.22/13.43          | ~ (v1_xboole_0 @ X1)
% 13.22/13.43          | ~ (v1_xboole_0 @ X2))),
% 13.22/13.43      inference('sup+', [status(thm)], ['65', '66'])).
% 13.22/13.43  thf('68', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X0)
% 13.22/13.43          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k2_zfmisc_1 @ X0 @ X1)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['62', '67'])).
% 13.22/13.43  thf('69', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('sup+', [status(thm)], ['63', '64'])).
% 13.22/13.43  thf('70', plain,
% 13.22/13.43      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('demod', [status(thm)], ['23', '25'])).
% 13.22/13.43  thf('71', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.43         (((k1_xboole_0) = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))
% 13.22/13.43          | ~ (v1_xboole_0 @ X1))),
% 13.22/13.43      inference('sup+', [status(thm)], ['69', '70'])).
% 13.22/13.43  thf('72', plain,
% 13.22/13.43      (![X0 : $i, X2 : $i]:
% 13.22/13.43         (((k1_xboole_0)
% 13.22/13.43            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ X0))
% 13.22/13.43          | ~ (v1_xboole_0 @ X2)
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X2))),
% 13.22/13.43      inference('sup+', [status(thm)], ['68', '71'])).
% 13.22/13.43  thf('73', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('74', plain,
% 13.22/13.43      (![X0 : $i, X2 : $i]:
% 13.22/13.43         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0))
% 13.22/13.43          | ~ (v1_xboole_0 @ X2)
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X2))),
% 13.22/13.43      inference('demod', [status(thm)], ['72', '73'])).
% 13.22/13.43  thf('75', plain,
% 13.22/13.43      (![X0 : $i, X2 : $i]:
% 13.22/13.43         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X2)
% 13.22/13.43          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)))),
% 13.22/13.43      inference('simplify', [status(thm)], ['74'])).
% 13.22/13.43  thf('76', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32) != (k1_xboole_0))
% 13.22/13.43          | ((X32) = (k1_xboole_0))
% 13.22/13.43          | ((X31) = (k1_xboole_0))
% 13.22/13.43          | ((X30) = (k1_xboole_0))
% 13.22/13.43          | ((X29) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('77', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (k1_xboole_0))
% 13.22/13.43          | ~ (v1_xboole_0 @ X1)
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((X0) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['75', '76'])).
% 13.22/13.43  thf('78', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X1))),
% 13.22/13.43      inference('simplify', [status(thm)], ['77'])).
% 13.22/13.43  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('81', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('82', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ~ (v1_xboole_0 @ X1))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)], ['78', '79', '80', '81'])).
% 13.22/13.43  thf('83', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 13.22/13.43          | ((X0) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['61', '82'])).
% 13.22/13.43  thf('84', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 13.22/13.43      inference('simplify', [status(thm)], ['83'])).
% 13.22/13.43  thf('85', plain,
% 13.22/13.43      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 13.22/13.43      inference('cnf', [status(esa)], [t1_subset])).
% 13.22/13.43  thf('86', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 13.22/13.43      inference('sup-', [status(thm)], ['84', '85'])).
% 13.22/13.43  thf('87', plain,
% 13.22/13.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.22/13.43         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 13.22/13.43           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_mcart_1])).
% 13.22/13.43  thf(t20_mcart_1, axiom,
% 13.22/13.43    (![A:$i]:
% 13.22/13.43     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 13.22/13.43       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 13.22/13.43  thf('88', plain,
% 13.22/13.43      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.22/13.43         (((X20) != (k2_mcart_1 @ X20)) | ((X20) != (k4_tarski @ X21 @ X22)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t20_mcart_1])).
% 13.22/13.43  thf('89', plain,
% 13.22/13.43      (![X21 : $i, X22 : $i]:
% 13.22/13.43         ((k4_tarski @ X21 @ X22) != (k2_mcart_1 @ (k4_tarski @ X21 @ X22)))),
% 13.22/13.43      inference('simplify', [status(thm)], ['88'])).
% 13.22/13.43  thf(t7_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i]:
% 13.22/13.43     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 13.22/13.43       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 13.22/13.43  thf('90', plain,
% 13.22/13.43      (![X34 : $i, X36 : $i]: ((k2_mcart_1 @ (k4_tarski @ X34 @ X36)) = (X36))),
% 13.22/13.43      inference('cnf', [status(esa)], [t7_mcart_1])).
% 13.22/13.43  thf('91', plain, (![X21 : $i, X22 : $i]: ((k4_tarski @ X21 @ X22) != (X22))),
% 13.22/13.43      inference('demod', [status(thm)], ['89', '90'])).
% 13.22/13.43  thf('92', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 13.22/13.43      inference('sup-', [status(thm)], ['87', '91'])).
% 13.22/13.43  thf('93', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (X0))
% 13.22/13.43          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 13.22/13.43      inference('sup-', [status(thm)], ['86', '92'])).
% 13.22/13.43  thf('94', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 13.22/13.43      inference('simplify', [status(thm)], ['93'])).
% 13.22/13.43  thf('95', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 13.22/13.43          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43          | ((sk_D) = (X0))
% 13.22/13.43          | ~ (m1_subset_1 @ X0 @ sk_C)
% 13.22/13.43          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('demod', [status(thm)], ['58', '94'])).
% 13.22/13.43  thf('96', plain,
% 13.22/13.43      ((((sk_E) != (sk_E))
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 13.22/13.43        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 13.22/13.43        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 13.22/13.43        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['37', '95'])).
% 13.22/13.43  thf('97', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['1', '2'])).
% 13.22/13.43  thf('98', plain,
% 13.22/13.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 13.22/13.43         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 13.22/13.43           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 13.22/13.43      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 13.22/13.43  thf('99', plain,
% 13.22/13.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 13.22/13.43         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 13.22/13.43          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t10_mcart_1])).
% 13.22/13.43  thf('100', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.22/13.43         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 13.22/13.43          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 13.22/13.43      inference('sup-', [status(thm)], ['98', '99'])).
% 13.22/13.43  thf('101', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('sup-', [status(thm)], ['97', '100'])).
% 13.22/13.43  thf('102', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('103', plain,
% 13.22/13.43      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['101', '102'])).
% 13.22/13.43  thf('104', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('105', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)
% 13.22/13.43            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 13.22/13.43          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('sup+', [status(thm)], ['103', '104'])).
% 13.22/13.43  thf('106', plain,
% 13.22/13.43      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('demod', [status(thm)], ['23', '25'])).
% 13.22/13.43  thf('107', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0) = (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('demod', [status(thm)], ['105', '106'])).
% 13.22/13.43  thf('108', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32) != (k1_xboole_0))
% 13.22/13.43          | ((X32) = (k1_xboole_0))
% 13.22/13.43          | ((X31) = (k1_xboole_0))
% 13.22/13.43          | ((X30) = (k1_xboole_0))
% 13.22/13.43          | ((X29) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('109', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((X0) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['107', '108'])).
% 13.22/13.43  thf('110', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('simplify', [status(thm)], ['109'])).
% 13.22/13.43  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('112', plain, (((sk_B) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('113', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('114', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0)) | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)],
% 13.22/13.43                ['110', '111', '112', '113'])).
% 13.22/13.43  thf('115', plain,
% 13.22/13.43      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 13.22/13.43      inference('cnf', [status(esa)], [t1_subset])).
% 13.22/13.43  thf('116', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('sup-', [status(thm)], ['114', '115'])).
% 13.22/13.43  thf('117', plain,
% 13.22/13.43      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 13.22/13.43      inference('sup-', [status(thm)], ['87', '91'])).
% 13.22/13.43  thf('118', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (X0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 13.22/13.43      inference('sup-', [status(thm)], ['116', '117'])).
% 13.22/13.43  thf('119', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 13.22/13.43      inference('simplify', [status(thm)], ['118'])).
% 13.22/13.43  thf('120', plain,
% 13.22/13.43      ((((sk_E) != (sk_E))
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 13.22/13.43        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 13.22/13.43        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 13.22/13.43      inference('demod', [status(thm)], ['96', '119'])).
% 13.22/13.43  thf('121', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('simplify', [status(thm)], ['120'])).
% 13.22/13.43  thf('122', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('123', plain,
% 13.22/13.43      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf(t50_mcart_1, axiom,
% 13.22/13.43    (![A:$i,B:$i,C:$i]:
% 13.22/13.43     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 13.22/13.43          ( ( C ) != ( k1_xboole_0 ) ) & 
% 13.22/13.43          ( ~( ![D:$i]:
% 13.22/13.43               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 13.22/13.43                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 13.22/13.43                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 13.22/13.43                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 13.22/13.43                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 13.22/13.43                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 13.22/13.43  thf('124', plain,
% 13.22/13.43      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 13.22/13.43         (((X25) = (k1_xboole_0))
% 13.22/13.43          | ((X26) = (k1_xboole_0))
% 13.22/13.43          | ((k7_mcart_1 @ X25 @ X26 @ X28 @ X27) = (k2_mcart_1 @ X27))
% 13.22/13.43          | ~ (m1_subset_1 @ X27 @ (k3_zfmisc_1 @ X25 @ X26 @ X28))
% 13.22/13.43          | ((X28) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t50_mcart_1])).
% 13.22/13.43  thf('125', plain,
% 13.22/13.43      ((((sk_C) = (k1_xboole_0))
% 13.22/13.43        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 13.22/13.43        | ((sk_B) = (k1_xboole_0))
% 13.22/13.43        | ((sk_A) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['123', '124'])).
% 13.22/13.43  thf('126', plain, (((sk_A) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('127', plain, (((sk_B) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('128', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('129', plain,
% 13.22/13.43      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)],
% 13.22/13.43                ['125', '126', '127', '128'])).
% 13.22/13.43  thf('130', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 13.22/13.43      inference('demod', [status(thm)], ['122', '129'])).
% 13.22/13.43  thf('131', plain,
% 13.22/13.43      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 13.22/13.43        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)], ['121', '130'])).
% 13.22/13.43  thf('132', plain,
% 13.22/13.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.22/13.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.22/13.43  thf('133', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))),
% 13.22/13.43      inference('clc', [status(thm)], ['131', '132'])).
% 13.22/13.43  thf('134', plain,
% 13.22/13.43      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 13.22/13.43           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 13.22/13.43      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 13.22/13.43  thf('135', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0)
% 13.22/13.43           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('sup+', [status(thm)], ['133', '134'])).
% 13.22/13.43  thf('136', plain,
% 13.22/13.43      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 13.22/13.43      inference('demod', [status(thm)], ['23', '25'])).
% 13.22/13.43  thf('137', plain,
% 13.22/13.43      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ X0) = (k1_xboole_0))),
% 13.22/13.43      inference('demod', [status(thm)], ['135', '136'])).
% 13.22/13.43  thf('138', plain,
% 13.22/13.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.22/13.43         (((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32) != (k1_xboole_0))
% 13.22/13.43          | ((X32) = (k1_xboole_0))
% 13.22/13.43          | ((X31) = (k1_xboole_0))
% 13.22/13.43          | ((X30) = (k1_xboole_0))
% 13.22/13.43          | ((X29) = (k1_xboole_0)))),
% 13.22/13.43      inference('cnf', [status(esa)], [t55_mcart_1])).
% 13.22/13.43  thf('139', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((k1_xboole_0) != (k1_xboole_0))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((X0) = (k1_xboole_0)))),
% 13.22/13.43      inference('sup-', [status(thm)], ['137', '138'])).
% 13.22/13.43  thf('140', plain,
% 13.22/13.43      (![X0 : $i]:
% 13.22/13.43         (((X0) = (k1_xboole_0))
% 13.22/13.43          | ((sk_C) = (k1_xboole_0))
% 13.22/13.43          | ((sk_B) = (k1_xboole_0))
% 13.22/13.43          | ((sk_A) = (k1_xboole_0)))),
% 13.22/13.43      inference('simplify', [status(thm)], ['139'])).
% 13.22/13.43  thf('141', plain, (((sk_A) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('142', plain, (((sk_B) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('143', plain, (((sk_C) != (k1_xboole_0))),
% 13.22/13.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.43  thf('144', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 13.22/13.43      inference('simplify_reflect-', [status(thm)],
% 13.22/13.43                ['140', '141', '142', '143'])).
% 13.22/13.43  thf('145', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 13.22/13.43      inference('demod', [status(thm)], ['0', '144'])).
% 13.22/13.43  thf('146', plain, ($false), inference('simplify', [status(thm)], ['145'])).
% 13.22/13.43  
% 13.22/13.43  % SZS output end Refutation
% 13.22/13.43  
% 13.22/13.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
