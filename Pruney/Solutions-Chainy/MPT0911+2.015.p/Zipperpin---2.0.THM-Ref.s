%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D6enCBDjZ5

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 310 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :   26
%              Number of atoms          : 1429 (4997 expanded)
%              Number of equality atoms :  183 ( 694 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34
        = ( k4_tarski @ ( k1_mcart_1 @ X34 ) @ ( k2_mcart_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('37',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34
        = ( k4_tarski @ ( k1_mcart_1 @ X34 ) @ ( k2_mcart_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('53',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('55',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X41 @ X42 @ X44 @ X43 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X41 @ X42 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ sk_B_2 )
      | ( sk_E
       != ( k3_mcart_1 @ X51 @ X50 @ X52 ) )
      | ( sk_D = X52 )
      | ~ ( m1_subset_1 @ X52 @ sk_C )
      | ~ ( m1_subset_1 @ X51 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('67',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X41 @ X42 @ X44 @ X43 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X41 @ X42 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','75'])).

thf('77',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('79',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X27 @ X28 @ X29 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('80',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X41 @ X42 @ X44 @ X43 )
        = ( k2_mcart_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X41 @ X42 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('83',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('90',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['83','84','85','86'])).

thf('93',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X45: $i,X46: $i,X47: $i,X49: $i] :
      ( ( X47 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X49 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('98',plain,(
    ! [X45: $i,X46: $i,X49: $i] :
      ( ( k4_zfmisc_1 @ X45 @ X46 @ k1_xboole_0 @ X49 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('100',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X45: $i,X46: $i,X47: $i,X49: $i] :
      ( ( X49 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X49 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('108',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','109'])).

thf('111',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','117'])).

thf('119',plain,(
    $false ),
    inference(simplify,[status(thm)],['118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D6enCBDjZ5
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 559 iterations in 0.310s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.52/0.76  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.52/0.76  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.52/0.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.52/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.76  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.52/0.76  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.76  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.52/0.76  thf(t71_mcart_1, conjecture,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76       ( ( ![F:$i]:
% 0.52/0.76           ( ( m1_subset_1 @ F @ A ) =>
% 0.52/0.76             ( ![G:$i]:
% 0.52/0.76               ( ( m1_subset_1 @ G @ B ) =>
% 0.52/0.76                 ( ![H:$i]:
% 0.52/0.76                   ( ( m1_subset_1 @ H @ C ) =>
% 0.52/0.76                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.52/0.76                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.52/0.76         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.52/0.76        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76          ( ( ![F:$i]:
% 0.52/0.76              ( ( m1_subset_1 @ F @ A ) =>
% 0.52/0.76                ( ![G:$i]:
% 0.52/0.76                  ( ( m1_subset_1 @ G @ B ) =>
% 0.52/0.76                    ( ![H:$i]:
% 0.52/0.76                      ( ( m1_subset_1 @ H @ C ) =>
% 0.52/0.76                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.52/0.76                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.52/0.76            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.52/0.76              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.52/0.76  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t34_mcart_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76          ( ![B:$i]:
% 0.52/0.76            ( ~( ( r2_hidden @ B @ A ) & 
% 0.52/0.76                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.76                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.52/0.76                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      (![X36 : $i]:
% 0.52/0.76         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X36) @ X36))),
% 0.52/0.76      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.52/0.76  thf(t10_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.52/0.76       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.52/0.76         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.76         ((r2_hidden @ (k1_mcart_1 @ X31) @ X32)
% 0.52/0.76          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ X32 @ X33)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.52/0.76          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.76  thf(d1_xboole_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X36 : $i]:
% 0.52/0.76         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X36) @ X36))),
% 0.52/0.76      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.52/0.76          | ~ (v1_xboole_0 @ X1)
% 0.52/0.76          | ~ (v1_xboole_0 @ X2))),
% 0.52/0.76      inference('sup+', [status(thm)], ['5', '8'])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t2_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (![X5 : $i, X6 : $i]:
% 0.52/0.76         ((r2_hidden @ X5 @ X6)
% 0.52/0.76          | (v1_xboole_0 @ X6)
% 0.52/0.76          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.52/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.76  thf(t23_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( v1_relat_1 @ B ) =>
% 0.52/0.76       ( ( r2_hidden @ A @ B ) =>
% 0.52/0.76         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (![X34 : $i, X35 : $i]:
% 0.52/0.76         (((X34) = (k4_tarski @ (k1_mcart_1 @ X34) @ (k2_mcart_1 @ X34)))
% 0.52/0.76          | ~ (v1_relat_1 @ X35)
% 0.52/0.76          | ~ (r2_hidden @ X34 @ X35))),
% 0.52/0.76      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.76  thf(d3_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.52/0.76       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.52/0.76           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.52/0.76  thf(fc6_relat_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['15', '16'])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('demod', [status(thm)], ['14', '17'])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.76  thf(d4_zfmisc_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.52/0.76       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.52/0.76           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.52/0.76            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.52/0.76          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('sup+', [status(thm)], ['20', '21'])).
% 0.52/0.76  thf(t55_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.52/0.76       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.52/0.76         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.52/0.76          | ((X48) = (k1_xboole_0))
% 0.52/0.76          | ((X47) = (k1_xboole_0))
% 0.52/0.76          | ((X46) = (k1_xboole_0))
% 0.52/0.76          | ((X45) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.52/0.76          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76          | ((sk_A) = (k1_xboole_0))
% 0.52/0.76          | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76          | ((sk_C) = (k1_xboole_0))
% 0.52/0.76          | ((X0) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.76  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('26', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.52/0.76          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76          | ((X0) = (k1_xboole_0)))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.52/0.76  thf('29', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((X0) != (k1_xboole_0))
% 0.52/0.76          | ~ (v1_xboole_0 @ X0)
% 0.52/0.76          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.76          | ((X1) = (k1_xboole_0))
% 0.52/0.76          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['9', '28'])).
% 0.52/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.76  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (((X0) != (k1_xboole_0))
% 0.52/0.76          | ~ (v1_xboole_0 @ X0)
% 0.52/0.76          | ((X1) = (k1_xboole_0))
% 0.52/0.76          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (![X1 : $i]:
% 0.52/0.76         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76          | ((X1) = (k1_xboole_0))
% 0.52/0.76          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.76  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X1 : $i]:
% 0.52/0.76         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76          | ((X1) = (k1_xboole_0)))),
% 0.52/0.76      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.52/0.76  thf('35', plain,
% 0.52/0.76      ((((k1_xboole_0) != (sk_E))
% 0.52/0.76        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.52/0.76      inference('eq_fact', [status(thm)], ['34'])).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      (![X1 : $i]:
% 0.52/0.76         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.52/0.76          | ((X1) = (k1_xboole_0)))),
% 0.52/0.76      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.52/0.76      inference('clc', [status(thm)], ['35', '36'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.52/0.76           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.76         ((r2_hidden @ (k1_mcart_1 @ X31) @ X32)
% 0.52/0.76          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ X32 @ X33)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.52/0.76          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.76  thf('42', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['38', '41'])).
% 0.52/0.76  thf('43', plain,
% 0.52/0.76      (![X34 : $i, X35 : $i]:
% 0.52/0.76         (((X34) = (k4_tarski @ (k1_mcart_1 @ X34) @ (k2_mcart_1 @ X34)))
% 0.52/0.76          | ~ (v1_relat_1 @ X35)
% 0.52/0.76          | ~ (r2_hidden @ X34 @ X35))),
% 0.52/0.76      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.52/0.76        | ((k1_mcart_1 @ sk_E)
% 0.52/0.76            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.52/0.76               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('45', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.52/0.76        | ((k1_mcart_1 @ sk_E)
% 0.52/0.76            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.52/0.76               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.52/0.76      inference('demod', [status(thm)], ['44', '45'])).
% 0.52/0.76  thf('47', plain,
% 0.52/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      ((((k1_mcart_1 @ sk_E)
% 0.52/0.76          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.52/0.76             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.52/0.76        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.76  thf(d3_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.76         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.52/0.76           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.52/0.76  thf('50', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.52/0.76            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.52/0.76            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.52/0.76          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['48', '49'])).
% 0.52/0.76  thf('51', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_k6_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k6_mcart_1 @ X23 @ X24 @ X25 @ X26) @ X24)
% 0.52/0.76          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X23 @ X24 @ X25)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.52/0.76  thf('53', plain,
% 0.52/0.76      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) @ sk_B_2)),
% 0.52/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t50_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.52/0.76          ( ~( ![D:$i]:
% 0.52/0.76               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.52/0.76                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.52/0.76                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.52/0.76                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.52/0.76                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.76         (((X41) = (k1_xboole_0))
% 0.52/0.76          | ((X42) = (k1_xboole_0))
% 0.52/0.76          | ((k6_mcart_1 @ X41 @ X42 @ X44 @ X43)
% 0.52/0.76              = (k2_mcart_1 @ (k1_mcart_1 @ X43)))
% 0.52/0.76          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X41 @ X42 @ X44))
% 0.52/0.76          | ((X44) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      ((((sk_C) = (k1_xboole_0))
% 0.52/0.76        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.52/0.76            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.52/0.76        | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.76  thf('57', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('58', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.52/0.76         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['56', '57', '58', '59'])).
% 0.52/0.76  thf('61', plain,
% 0.52/0.76      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)),
% 0.52/0.76      inference('demod', [status(thm)], ['53', '60'])).
% 0.52/0.76  thf('62', plain,
% 0.52/0.76      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X50 @ sk_B_2)
% 0.52/0.76          | ((sk_E) != (k3_mcart_1 @ X51 @ X50 @ X52))
% 0.52/0.76          | ((sk_D) = (X52))
% 0.52/0.76          | ~ (m1_subset_1 @ X52 @ sk_C)
% 0.52/0.76          | ~ (m1_subset_1 @ X51 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('63', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.52/0.76          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.52/0.76          | ((sk_D) = (X1))
% 0.52/0.76          | ((sk_E)
% 0.52/0.76              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['61', '62'])).
% 0.52/0.76  thf('64', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.52/0.76          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.52/0.76          | ((sk_D) = (X0))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.52/0.76          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.52/0.76      inference('sup-', [status(thm)], ['50', '63'])).
% 0.52/0.76  thf('65', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_k5_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.52/0.76  thf('66', plain,
% 0.52/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k5_mcart_1 @ X19 @ X20 @ X21 @ X22) @ X19)
% 0.52/0.76          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X19 @ X20 @ X21)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.52/0.76  thf('67', plain,
% 0.52/0.76      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) @ sk_A)),
% 0.52/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.52/0.76  thf('68', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('69', plain,
% 0.52/0.76      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.76         (((X41) = (k1_xboole_0))
% 0.52/0.76          | ((X42) = (k1_xboole_0))
% 0.52/0.76          | ((k5_mcart_1 @ X41 @ X42 @ X44 @ X43)
% 0.52/0.76              = (k1_mcart_1 @ (k1_mcart_1 @ X43)))
% 0.52/0.76          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X41 @ X42 @ X44))
% 0.52/0.76          | ((X44) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.76  thf('70', plain,
% 0.52/0.76      ((((sk_C) = (k1_xboole_0))
% 0.52/0.76        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.52/0.76            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.52/0.76        | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.52/0.76  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('72', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('73', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('74', plain,
% 0.52/0.76      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E)
% 0.52/0.76         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['70', '71', '72', '73'])).
% 0.52/0.76  thf('75', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.52/0.76      inference('demod', [status(thm)], ['67', '74'])).
% 0.52/0.76  thf('76', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.52/0.76          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.52/0.76          | ((sk_D) = (X0))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.52/0.76      inference('demod', [status(thm)], ['64', '75'])).
% 0.52/0.76  thf('77', plain,
% 0.52/0.76      ((((sk_E) != (sk_E))
% 0.52/0.76        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.52/0.76        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.52/0.76        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['37', '76'])).
% 0.52/0.76  thf('78', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_k7_mcart_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.52/0.76       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.52/0.76  thf('79', plain,
% 0.52/0.76      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k7_mcart_1 @ X27 @ X28 @ X29 @ X30) @ X29)
% 0.52/0.76          | ~ (m1_subset_1 @ X30 @ (k3_zfmisc_1 @ X27 @ X28 @ X29)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.52/0.76  thf('80', plain,
% 0.52/0.76      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) @ sk_C)),
% 0.52/0.76      inference('sup-', [status(thm)], ['78', '79'])).
% 0.52/0.76  thf('81', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('82', plain,
% 0.52/0.76      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.76         (((X41) = (k1_xboole_0))
% 0.52/0.76          | ((X42) = (k1_xboole_0))
% 0.52/0.76          | ((k7_mcart_1 @ X41 @ X42 @ X44 @ X43) = (k2_mcart_1 @ X43))
% 0.52/0.76          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X41 @ X42 @ X44))
% 0.52/0.76          | ((X44) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.52/0.76  thf('83', plain,
% 0.52/0.76      ((((sk_C) = (k1_xboole_0))
% 0.52/0.76        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.52/0.76        | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['81', '82'])).
% 0.52/0.76  thf('84', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('85', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('86', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('87', plain,
% 0.52/0.76      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['83', '84', '85', '86'])).
% 0.52/0.76  thf('88', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.52/0.76      inference('demod', [status(thm)], ['80', '87'])).
% 0.52/0.76  thf('89', plain,
% 0.52/0.76      ((((sk_E) != (sk_E))
% 0.52/0.76        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.52/0.76        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.76      inference('demod', [status(thm)], ['77', '88'])).
% 0.52/0.76  thf('90', plain,
% 0.52/0.76      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.52/0.76        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['89'])).
% 0.52/0.76  thf('91', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('92', plain,
% 0.52/0.76      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['83', '84', '85', '86'])).
% 0.52/0.76  thf('93', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.52/0.76      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.76  thf('94', plain, (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.52/0.76  thf('95', plain,
% 0.52/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.52/0.76           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.52/0.76  thf('96', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.52/0.76           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['94', '95'])).
% 0.52/0.76  thf('97', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X47 : $i, X49 : $i]:
% 0.52/0.76         (((X47) != (k1_xboole_0))
% 0.52/0.76          | ((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X49) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.52/0.76  thf('98', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X49 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X45 @ X46 @ k1_xboole_0 @ X49) = (k1_xboole_0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['97'])).
% 0.52/0.76  thf('99', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.52/0.76           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.52/0.76  thf('100', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.52/0.76           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.52/0.76  thf('101', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.52/0.76           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.52/0.76      inference('sup+', [status(thm)], ['99', '100'])).
% 0.52/0.76  thf('102', plain,
% 0.52/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.52/0.76           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.52/0.76  thf('103', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.52/0.76           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.52/0.76      inference('demod', [status(thm)], ['101', '102'])).
% 0.52/0.76  thf('104', plain,
% 0.52/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.52/0.76           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.52/0.76  thf('105', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.52/0.76           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.52/0.76      inference('sup+', [status(thm)], ['103', '104'])).
% 0.52/0.76  thf('106', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         ((k1_xboole_0)
% 0.52/0.76           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['98', '105'])).
% 0.52/0.76  thf('107', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X47 : $i, X49 : $i]:
% 0.52/0.76         (((X49) != (k1_xboole_0))
% 0.52/0.76          | ((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X49) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.52/0.76  thf('108', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.52/0.76         ((k4_zfmisc_1 @ X45 @ X46 @ X47 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['107'])).
% 0.52/0.76  thf('109', plain,
% 0.52/0.76      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['106', '108'])).
% 0.52/0.76  thf('110', plain,
% 0.52/0.76      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['96', '109'])).
% 0.52/0.76  thf('111', plain,
% 0.52/0.76      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.52/0.76         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.52/0.76          | ((X48) = (k1_xboole_0))
% 0.52/0.76          | ((X47) = (k1_xboole_0))
% 0.52/0.76          | ((X46) = (k1_xboole_0))
% 0.52/0.76          | ((X45) = (k1_xboole_0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.52/0.76  thf('112', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.76          | ((sk_A) = (k1_xboole_0))
% 0.52/0.76          | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76          | ((sk_C) = (k1_xboole_0))
% 0.52/0.76          | ((X0) = (k1_xboole_0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['110', '111'])).
% 0.52/0.76  thf('113', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((X0) = (k1_xboole_0))
% 0.52/0.76          | ((sk_C) = (k1_xboole_0))
% 0.52/0.76          | ((sk_B_2) = (k1_xboole_0))
% 0.52/0.76          | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['112'])).
% 0.52/0.76  thf('114', plain, (((sk_A) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('115', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('116', plain, (((sk_C) != (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('117', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.52/0.76      inference('simplify_reflect-', [status(thm)],
% 0.52/0.76                ['113', '114', '115', '116'])).
% 0.52/0.76  thf('118', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.76      inference('demod', [status(thm)], ['0', '117'])).
% 0.52/0.76  thf('119', plain, ($false), inference('simplify', [status(thm)], ['118'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
